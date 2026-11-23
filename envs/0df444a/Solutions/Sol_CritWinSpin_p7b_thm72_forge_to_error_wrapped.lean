-- Prove2me | solution 1 for CritWinSpin.p7b_thm72_forge_to_error_wrapped
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:27:13.964073+00:00
-- url     : https://prove2.me/submissions/bcc59225-1cc7-4ae1-aa81-18dd094f5e1f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Theorems.Thm_CritWinSpin_p7b_7_2_prob_reduction
import Theorems.Thm_CritWinSpin_p7b_7_2_forger_impl

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
open CritWinSpin
set_option autoImplicit false
set_option linter.unusedVariables false

namespace CritWinSpin

private lemma wrapped_ppt_prob_nonneg (A : PPT) (u : Str) (E : Str → Prop) : 0 ≤ A.prob u E := by
  unfold OWFLocalDesc.PPT.prob
  positivity

private lemma wrapped_prob_partition {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (g : (Fin m → Bool) → α) :
    ∑ o : α, ((Finset.univ.filter fun ρ : Fin m → Bool => g ρ = o).card : ℝ) / (2 : ℝ) ^ m = 1 := by
  have hsum_card :
      ∑ o : α, (Finset.univ.filter fun ρ : Fin m → Bool => g ρ = o).card =
        (Finset.univ : Finset (Fin m → Bool)).card :=
    (Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _).symm
  have hcard_univ : ((Finset.univ : Finset (Fin m → Bool)).card : ℝ) = (2 : ℝ) ^ m := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [← Finset.sum_div, ← Nat.cast_sum, hsum_card, hcard_univ, div_self (by positivity)]

private lemma wrapped_ppt_fiber_sum_one {α : Type*} [Fintype α] [DecidableEq α]
    (A : PPT) (u : Str) (dec : Str → α) :
    ∑ o : α, A.prob u (fun s => dec s = o) = 1 := by
  unfold OWFLocalDesc.PPT.prob
  let m := Polynomial.eval u.length A.coins
  let f : (Fin m → Bool) → α := fun ρ => dec (A.alg (tupleCode [List.ofFn ρ, u]))
  convert wrapped_prob_partition m f

end CritWinSpin

theorem solution (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (F : BilinearFamily) (src : BinarySource F) (C : ℝ) (hC : 0 < C) (hsrc : SourceProps F src C)
    (w ε : ℝ) (Ac Cc : ℕ) (hw : 1 ≤ w) (hε : 0 < ε) (hεd : ε < dExp p)
    (hpar : GadgetParams p w ε Ac Cc)
    (Ccap : ℝ) (hCcap : 0 < Ccap)
    (liftF : Str → Str) (hliftF : CookPvsNP.PolyTimeComputable liftF) (slotM : PPT)
    (û : (d : ℕ) → (desc : Str) → WatersKey F desc d → ℚ) (d₁ : ℕ)
    (hlift : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      IsUhat S ((thetaQ p Ac Cc (src.n d) : ℚ) : ℝ) (cloudSize p Cc (src.n d)) (û d desc key) ∧
      liftF (encInst (src.ham d desc key)) =
        tupleCode [encInst (liftInst S p Ac Cc (src.ham d desc key) (û d desc key)),
          encRat (û d desc key)])
    (hdec : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      LhatDecodes (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key)))
    (k T : ℕ → ℕ) (hk : EffPoly k) (hk₁ : ∀ d, 1 ≤ k d) (hT : EffPoly T)
    (hTk : ∀ d, ⌈Ccap * ((k d : ℝ) + 1 + (src.n d : ℝ) ^ 2)⌉₊ ≤ T d)
    (v₁ v₂ : ℕ → ℝ)
    (hv₁ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
          (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (k d))
        (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
          (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (k d)) ≤ v₁ d)
    (hv₂ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
          (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (k d + 1))
        (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
          (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (k d + 1)) ≤ v₂ d)
    (A : PPT) :
    (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
      1 - forgeProb src B (T d) d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errExt S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) ∧
    (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
      1 - forgeProb src B (T d) d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errAmp S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) := by
  have hT1 : ∀ d, 1 ≤ T d := fun d => by
    have hpos : (0 : ℝ) < Ccap * ((k d : ℝ) + 1 + (src.n d : ℝ) ^ 2) :=
      mul_pos hCcap (by positivity)
    exact (Nat.succ_le_of_lt (Nat.ceil_pos.mpr hpos)).trans (hTk d)
  let K_ext : (d : ℕ) → Inst (src.n d * cloudSize p Cc (src.n d)) →
      (Fin (k d) → Config S (Fin (src.n d * cloudSize p Cc (src.n d)))) →
      Option (Config S (Fin (src.n d * cloudSize p Cc (src.n d)))) → ℝ :=
    fun d M X o => A.prob (tupleCode [encInst M, encSamples X])
      (fun s => decConfig S (src.n d * cloudSize p Cc (src.n d)) s = o)
  let K_amp : (d : ℕ) → Inst (src.n d * cloudSize p Cc (src.n d)) →
      (Fin (k d) → Config S (Fin (src.n d * cloudSize p Cc (src.n d)))) →
      Option (Fin (k d + 1) → Config S (Fin (src.n d * cloudSize p Cc (src.n d)))) → ℝ :=
    fun d M X o => A.prob (tupleCode [encInst M, encSamples X])
      (fun s => decTuple S (src.n d * cloudSize p Cc (src.n d)) (k d + 1) s = o)
  have hKe0 : ∀ d M X o, 0 ≤ K_ext d M X o := fun d M X o => CritWinSpin.wrapped_ppt_prob_nonneg A _ _
  have hKe1 : ∀ d M X, ∑ o, K_ext d M X o = 1 := fun d M X => CritWinSpin.wrapped_ppt_fiber_sum_one A _ _
  have hKa0 : ∀ d M X o, 0 ≤ K_amp d M X o := fun d M X o => CritWinSpin.wrapped_ppt_prob_nonneg A _ _
  have hKa1 : ∀ d M X, ∑ o, K_amp d M X o = 1 := fun d M X => CritWinSpin.wrapped_ppt_fiber_sum_one A _ _
  obtain ⟨B_ext, B_amp, hforger_ext, hforger_amp⟩ :=
    p7b_7_2_forger_impl S p F src C hsrc Ac Cc Ccap hCcap liftF hliftF slotM û d₁ hlift
      k T hk hk₁ hT hTk A
  let score_ext : (d : ℕ) → (desc : Str) → WatersKey F desc d →
      (Fin (T d) → BinCfg (src.n d)) → ℝ :=
    fun d desc key Fs =>
      B_ext.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
        (fun s => ∃ y : BinCfg (src.n d), s = List.ofFn y ∧ y ∈ src.omega d desc key ∧
          ∀ t, src.psi d desc key y ≠ src.psi d desc key (Fs t))
  let score_amp : (d : ℕ) → (desc : Str) → WatersKey F desc d →
      (Fin (T d) → BinCfg (src.n d)) → ℝ :=
    fun d desc key Fs =>
      B_amp.prob (tupleCode (pkCode F d desc key :: List.ofFn fun t => List.ofFn (Fs t)))
        (fun s => ∃ y : BinCfg (src.n d), s = List.ofFn y ∧ y ∈ src.omega d desc key ∧
          ∀ t, src.psi d desc key y ≠ src.psi d desc key (Fs t))
  have hred := p7b_7_2_prob_reduction S p F src C hsrc Ac Cc slotM û (max 1 d₁)
    (fun d hd => hdec d (le_trans (le_max_right _ _) hd))
    k T hT1 v₁ v₂
    (fun d hd => hv₁ d (le_trans (le_max_right _ _) hd))
    (fun d hd => hv₂ d (le_trans (le_max_right _ _) hd))
    K_ext hKe0 hKe1 K_amp hKa0 hKa1 score_ext score_amp hforger_ext hforger_amp
  refine ⟨⟨B_ext, max 1 (max 1 d₁), fun d hd => ?_⟩,
    ⟨B_amp, max 1 (max 1 d₁), fun d hd => ?_⟩⟩
  · exact (hred d hd).1
  · exact (hred d hd).2
