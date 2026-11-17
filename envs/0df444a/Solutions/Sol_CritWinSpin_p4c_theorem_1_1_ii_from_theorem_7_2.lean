-- Prove2me | solution 1 for CritWinSpin.p4c_theorem_1_1_ii_from_theorem_7_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-16T07:58:03.743577+00:00
-- url     : https://prove2.me/submissions/c178a065-438f-44f7-832e-312cbe02761b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_CritWinSpin_encInst
import Definitions.Def_CritWinSpin_RandMachine
import Definitions.Def_CritWinSpin_BilinearFamily
import Definitions.Def_CritWinSpin_errExt
import Definitions.Def_CritWinSpin_Lhat
import Theorems.Thm_CritWinSpin_theorem_5_1
import Theorems.Thm_CritWinSpin_theorem_6_3
import Theorems.Thm_CritWinSpin_p4c_1_1_ii_asymptotics
import Theorems.Thm_CritWinSpin_p4c_1_1_ii_ppt_wrappers

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace CritWinSpin

private lemma p4c11d_ppt_prob_nonneg (A : PPT) (u : Str) (E : Str → Prop) : 0 ≤ A.prob u E := by
  unfold OWFLocalDesc.PPT.prob
  positivity

private lemma p4c11d_prob_partition {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (g : (Fin m → Bool) → α) :
    ∑ o : α, ((Finset.univ.filter fun ρ : Fin m → Bool => g ρ = o).card : ℝ) / (2 : ℝ) ^ m = 1 := by
  have hsum_card :
      ∑ o : α, (Finset.univ.filter fun ρ : Fin m → Bool => g ρ = o).card =
        (Finset.univ : Finset (Fin m → Bool)).card :=
    (Finset.card_eq_sum_card_fiberwise fun _ _ => Finset.mem_univ _).symm
  have hcard_univ : ((Finset.univ : Finset (Fin m → Bool)).card : ℝ) = (2 : ℝ) ^ m := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Finset.sum_div, ← Nat.cast_sum, hsum_card, hcard_univ, div_self (by positivity)]

private lemma p4c11d_ppt_fiber_sum_one {α : Type*} [Fintype α] [DecidableEq α]
    (A : PPT) (u : Str) (dec : Str → α) :
    ∑ o : α, A.prob u (fun s => dec s = o) = 1 := by
  unfold OWFLocalDesc.PPT.prob
  let m := Polynomial.eval u.length A.coins
  let f : (Fin m → Bool) → α := fun ρ => dec (A.alg (tupleCode [List.ofFn ρ, u]))
  convert p4c11d_prob_partition m f

private lemma p4c11d_liftInst_isSymm (S : SpinLaw) (p Ac Cc : ℕ) {n : ℕ} (H : Inst n)
    (û : ℚ) (hH : H.1.IsSymm) :
    (liftInst S p Ac Cc H û).1.IsSymm := by
  unfold liftInst liftJQ liftJ
  ext a b
  simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
  have hsym := congrFun (congrFun hH (finProdFinEquiv.symm a).1) (finProdFinEquiv.symm b).1
  have hsym' : H.1 (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm a).1 =
      H.1 (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm b).1 := by
    simpa [Matrix.transpose_apply] using hsym
  rw [hsym']
  by_cases h : (finProdFinEquiv.symm b).1 = (finProdFinEquiv.symm a).1
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem p4c_theorem_1_1_ii_decomp (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (hP : ∀ (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
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
      (A : PPT), (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
        1 - C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d -
            ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
            2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
          errExt S (keyLiftLaw F d fun desc key =>
            liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) ∧
      (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
        1 - C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d -
            ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
            2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
          errAmp S (keyLiftLaw F d fun desc key =>
            liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d))) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∀ ε : ℝ, 0 < ε → ε < dExp p → ∀ F : BilinearFamily, CDH F →
      ∃ (Fam : PPT) (Nf : ℕ → ℕ),
        (∀ d, d ≤ Nf d) ∧ PolyBounded Nf ∧
        (∀ d, 1 ≤ d → ∀ ω : Fin (Fam.coins.eval (unary d).length) → Bool,
          ∃ I : Inst (Nf d), Fam.alg (tupleCode [List.ofFn ω, unary d]) = encInst I ∧
            I.1.IsSymm ∧ I.2 = 0 ∧ (castM I.1).PosSemidef ∧
            ((tau S * (1 + (Nf d : ℝ) ^ (-dExp p + ε))) •
                (1 : Matrix (Fin (Nf d)) (Fin (Nf d)) ℝ) - castM I.1).PosSemidef ∧
            width (castM I.1) (castV I.2) ≤ Cρ) ∧
        ∀ (A : PPT) (k : ℕ → ℕ), (∀ d, 1 ≤ k d) → PolyBounded k →
          (∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
            1 - errExt S (famLaw Fam (Nf d) d) A (k d) ≤ 1 / (Nf d : ℝ) ^ c) ∧
          (∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
            1 - errAmp S (famLaw Fam (Nf d) d) A (k d) ≤ 1 / (Nf d : ℝ) ^ c) := by
  classical
  obtain ⟨hGP, hNf_props, hPolyB, hZeroInst, hKeyLift, hPrefixExt, hPrefixAmp, hNegl, hShiftExt, hShiftAmp⟩ :=
    p4c_1_1_ii_asymptotics
  obtain ⟨hEffPoly, hFamWrap, hPrefixWrap⟩ := p4c_1_1_ii_ppt_wrappers
  obtain ⟨Cρ, Ccap, Cv, hCρ, hCcap, hCv, h63⟩ := theorem_6_3 S p hS hp
  obtain ⟨C₅₁, hC₅₁, h51⟩ := theorem_5_1
  refine ⟨Cρ, hCρ, fun ε hε hεd F hCDH => ?_⟩
  obtain ⟨circ, hcirc_poly, hcirc_sq, _, _, _, _, hsrc_hat, _⟩ := h51 F
  let src : BinarySource F := hatSource circ.toSource
  have hsrc_eq : src = hatSource circ.toSource := rfl
  have hn_eq : ∀ d, src.n d = circ.n0 d + 1 := fun _ => rfl
  have hn0_eq : ∀ d, src.n0 d = circ.n0 d := fun _ => rfl
  have hh_zero : ∀ d desc (key : WatersKey F desc d), (src.ham d desc key).2 = 0 := fun d desc key => rfl
  obtain ⟨w_src, hw_src1, hsrc_ham⟩ := hsrc_hat.1
  have hw_srcR : (1 : ℝ) ≤ (w_src : ℝ) := by exact_mod_cast hw_src1
  obtain ⟨Ac, Cc, hpar⟩ := hGP p hp.1 (w_src : ℝ) ε hw_srcR hε hεd
  obtain ⟨liftF, slotM, n₀_63, hliftF, h63_props⟩ := h63 (w_src : ℝ) ε Ac Cc hw_srcR hε hεd hpar
  let Nf : ℕ → ℕ := fun d => src.n d * cloudSize p Cc (src.n d)
  have hNf_def : ∀ d, Nf d = (circ.n0 d + 1) * cloudSize p Cc (circ.n0 d + 1) := fun _ => rfl
  obtain ⟨hNf_le, hNf_poly⟩ := hNf_props p circ.n0 hcirc_poly hcirc_sq Cc
  let d₁ : ℕ := max 1 n₀_63
  have hd₁_pos : 1 ≤ d₁ := le_max_left _ _
  have hnd_ge : ∀ d ≥ d₁, n₀_63 ≤ src.n d := by
    intro d hd
    have h1 : 1 ≤ d := hd₁_pos.trans hd
    have h2 : n₀_63 ≤ d := (le_max_right 1 n₀_63).trans hd
    have h3 : d ≤ d ^ 2 := by simpa [sq] using Nat.mul_le_mul_left d h1
    have h4 : d ^ 2 ≤ circ.n0 d := hcirc_sq d
    rw [hn_eq]
    omega
  have h63_at : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      (∀ û : ℚ, IsUhat S ((thetaQ p Ac Cc (src.n d) : ℚ) : ℝ) (cloudSize p Cc (src.n d)) û →
        (castM (liftInst S p Ac Cc (src.ham d desc key) û).1).PosSemidef ∧
        ((tau S * (1 + ((Nf d : ℕ) : ℝ) ^ (-dExp p + ε))) •
            (1 : Matrix (Fin (Nf d)) (Fin (Nf d)) ℝ) -
          castM (liftInst S p Ac Cc (src.ham d desc key) û).1).PosSemidef ∧
        width (castM (liftInst S p Ac Cc (src.ham d desc key) û).1)
          (castV (liftInst S p Ac Cc (src.ham d desc key) û).2) ≤ Cρ ∧
        ((src.ham d desc key).2 = 0 → (liftInst S p Ac Cc (src.ham d desc key) û).2 = 0)) ∧
      (∃ û : ℚ, IsUhat S ((thetaQ p Ac Cc (src.n d) : ℚ) : ℝ) (cloudSize p Cc (src.n d)) û ∧
        liftF (encInst (src.ham d desc key)) =
          tupleCode [encInst (liftInst S p Ac Cc (src.ham d desc key) û), encRat û]) ∧
      (∀ û : ℚ, IsUhat S ((thetaQ p Ac Cc (src.n d) : ℚ) : ℝ) (cloudSize p Cc (src.n d)) û →
        (∀ y : BinCfg (src.n d),
          tvDist (slotKernel S p Cc slotM (src.ham d desc key) û y)
              (idealSlot S (((tauQ S + thetaQ p Ac Cc (src.n d) : ℚ) : ℝ))
                (castM (src.ham d desc key).1) (castV (src.ham d desc key).2) (û : ℝ) y) ≤
            Real.exp (-(2 * (src.n d : ℝ) ^ 2))) ∧
        LhatDecodes (slotKernel S p Cc slotM (src.ham d desc key) û) ∧
        ∀ k T : ℕ, 1 ≤ k → ⌈Ccap * ((k : ℝ) + (src.n d : ℝ) ^ 2)⌉₊ ≤ T →
          tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) û)
              (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) T k)
            (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) û))
              (castV (liftHQ p Cc (src.ham d desc key) û)) k) ≤
            Cv * (T : ℝ) * Real.exp (-((src.n d : ℝ) ^ 2))) := by
    intro d hd desc hg key
    have hd1 : 1 ≤ d := hd₁_pos.trans hd
    obtain ⟨hsym, hdiag, hw⟩ := hsrc_ham d hd1 desc hg key
    have hw' : width (castM (src.ham d desc key).1) (castV (src.ham d desc key).2) ≤ (src.n d : ℝ) ^ (w_src : ℝ) := by
      simpa only [Real.rpow_natCast] using hw
    exact h63_props (src.n d) (src.ham d desc key) (hnd_ge d hd) hsym hdiag hw'
  let û : (d : ℕ) → (desc : Str) → WatersKey F desc d → ℚ := fun d desc key =>
    if h : ∃ hd : d₁ ≤ d, ∃ hg : GenSupport F.gen d desc, True then
      Classical.choose (h63_at d h.1 desc h.2.1 key).2.1
    else 0
  have hlift : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
      IsUhat S ((thetaQ p Ac Cc (src.n d) : ℚ) : ℝ) (cloudSize p Cc (src.n d)) (û d desc key) ∧
      liftF (encInst (src.ham d desc key)) =
        tupleCode [encInst (liftInst S p Ac Cc (src.ham d desc key) (û d desc key)),
          encRat (û d desc key)] := by
    intro d hd desc hg key
    dsimp [û]
    rw [dif_pos ⟨hd, hg, trivial⟩]
    exact Classical.choose_spec (h63_at d hd desc hg key).2.1
  obtain ⟨Fam, hFam_lo, hFam_hi⟩ :=
    hFamWrap S p Ac Cc F src liftF hliftF û d₁ hd₁_pos (fun d hd desc hg key => (hlift d hd desc hg key).2)
  refine ⟨Fam, Nf, hNf_le, hNf_poly, fun d hd1 ω => ?_, fun A k hk1 hk_poly => ?_⟩
  · by_cases hdd₁ : d < d₁
    · refine ⟨(0, 0), hFam_lo d hd1 hdd₁ ω, ?_⟩
      exact hZeroInst S p (Nf d) ε Cρ hCρ
    · have hge : d₁ ≤ d := le_of_not_gt hdd₁
      obtain ⟨desc, key, hg, halg⟩ := (hFam_hi d hge).1 ω
      have hu := (hlift d hge desc hg key).1
      obtain ⟨hpsd1, hpsd2, hwidth, hzero2⟩ := (h63_at d hge desc hg key).1 (û d desc key) hu
      have hsym_orig : (src.ham d desc key).1.IsSymm := (hsrc_ham d hd1 desc hg key).1
      refine ⟨liftInst S p Ac Cc (src.ham d desc key) (û d desc key), halg,
        p4c11d_liftInst_isSymm S p Ac Cc _ _ hsym_orig, hzero2 (hh_zero d desc key),
        hpsd1, hpsd2, hwidth⟩
  · have hsrc_n_poly : PolyBounded src.n := by
      change PolyBounded (fun d => circ.n0 d + 1)
      obtain ⟨k0, hk0⟩ := hcirc_poly
      refine ⟨k0 + 2, fun d => ?_⟩
      have h1 := hk0 d
      rcases eq_or_ne d 0 with rfl | hd0
      · rcases k0 with _ | k0
        · simp at h1 ⊢; omega
        · simp [Nat.zero_pow (Nat.succ_pos _)] at h1 ⊢; omega
      · have hd1 : 1 ≤ d := Nat.pos_of_ne_zero hd0
        have hp : d ^ k0 ≤ d ^ (k0 + 2) := Nat.pow_le_pow_right hd1 (by omega)
        have hd_ge : 1 ≤ d ^ (k0 + 2) := Nat.one_le_pow _ _ hd1
        dsimp
        omega
    obtain ⟨E, D₀, CT, hE1, hD₀1, hCT1, hD_prop, hT_prop⟩ :=
      hPolyB k src.n hk_poly hsrc_n_poly Ccap hCcap
    let D : ℕ → ℕ := fun d => 1 * d ^ E + D₀
    let T : ℕ → ℕ := fun d => CT * d ^ (2 * E) + CT
    have hD_eff : EffPoly D := hEffPoly 1 E D₀
    have hT_eff : EffPoly T := hEffPoly CT (2 * E) CT
    have hD_poly : PolyBounded D := hD_eff.1
    have hT_poly : PolyBounded T := hT_eff.1
    have hD1 : ∀ d, 1 ≤ D d := fun d => by simpa [D] using (hD_prop d).1
    have hkD : ∀ d, k d ≤ D d := fun d => by simpa [D] using (hD_prop d).2
    have hTD : ∀ d, ⌈Ccap * ((D d : ℝ) + 1 + (src.n d : ℝ) ^ 2)⌉₊ ≤ T d := fun d => by
      simpa [D, T] using (hT_prop d).2
    obtain ⟨A'_ext, A'_amp, w, R_ext, R_amp, hw_b, hRe0, hRe1, hRa0, hRa1, hA'_ext_eq, hA'_amp_eq⟩ :=
      hPrefixWrap S Nf k D hk1 hkD hD_poly A
    have hdec : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
        LhatDecodes (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key)) :=
      fun d hd desc hg key => ((h63_at d hd desc hg key).2.2 (û d desc key) (hlift d hd desc hg key).1).2.1
    let v₁ : ℕ → ℝ := fun d => Cv * (T d : ℝ) * Real.exp (-((src.n d : ℝ) ^ 2))
    let v₂ : ℕ → ℝ := fun d => Cv * (T d : ℝ) * Real.exp (-((src.n d : ℝ) ^ 2))
    have hv₁ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
        tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
            (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (D d))
          (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
            (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (D d)) ≤ v₁ d := by
      intro d hd desc hg key
      have hcap : ⌈Ccap * ((D d : ℝ) + (src.n d : ℝ) ^ 2)⌉₊ ≤ T d := by
        refine le_trans (Nat.ceil_mono ?_) (hTD d)
        exact mul_le_mul_of_nonneg_left (by linarith) hCcap.le
      exact ((h63_at d hd desc hg key).2.2 (û d desc key) (hlift d hd desc hg key).1).2.2 (D d) (T d) (hD1 d) hcap
    have hv₂ : ∀ d ≥ d₁, ∀ desc, GenSupport F.gen d desc → ∀ key : WatersKey F desc d,
        tvDist (LhatMu (slotKernel S p Cc slotM (src.ham d desc key) (û d desc key))
            (muH (castM (src.ham d desc key).1) (castV (src.ham d desc key).2)) (T d) (D d + 1))
          (gibbsTupleOpt S (castM (liftJQ S p Ac Cc (src.ham d desc key) (û d desc key)))
            (castV (liftHQ p Cc (src.ham d desc key) (û d desc key))) (D d + 1)) ≤ v₂ d := by
      intro d hd desc hg key
      have hcap : ⌈Ccap * ((D d + 1 : ℕ) + (src.n d : ℝ) ^ 2)⌉₊ ≤ T d := by
        refine le_trans (Nat.ceil_mono ?_) (hTD d)
        push_cast; linarith
      exact ((h63_at d hd desc hg key).2.2 (û d desc key) (hlift d hd desc hg key).1).2.2 (D d + 1) (T d) (by omega) hcap
    obtain ⟨h72_ext, _⟩ := hP S p hS hp F src C₅₁ hC₅₁ hsrc_hat (w_src : ℝ) ε Ac Cc hw_srcR hε hεd hpar
      Ccap hCcap liftF hliftF slotM û d₁ hlift hdec D T hD_eff hD1 hT_eff hTD v₁ v₂ hv₁ hv₂ A'_ext
    obtain ⟨_, h72_amp⟩ := hP S p hS hp F src C₅₁ hC₅₁ hsrc_hat (w_src : ℝ) ε Ac Cc hw_srcR hε hεd hpar
      Ccap hCcap liftF hliftF slotM û d₁ hlift hdec D T hD_eff hD1 hT_eff hTD v₁ v₂ hv₁ hv₂ A'_amp
    obtain ⟨B_ext, d₀_ext, hB_ext⟩ := h72_ext
    obtain ⟨B_amp, d₀_amp, hB_amp⟩ := h72_amp
    have hv_n0 : ∀ d, v₁ d ≤ Cv * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) := fun d => by
      dsimp [v₁]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg ?_)) (mul_nonneg hCv.le (Nat.cast_nonneg _))
      have hle : (src.n0 d : ℝ) ≤ (src.n d : ℝ) := by rw [hn0_eq, hn_eq]; push_cast; linarith
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hle 2
    constructor
    · refine hNegl Nf D T src.n0 v₁ v₂ (fun d => 1 - errExt S (famLaw Fam (Nf d) d) A (k d))
        C₅₁ Cv hC₅₁ hCv.le F B_ext hCDH hNf_le hNf_poly hD_poly hT_poly (fun d => by rw [hn0_eq]; exact hcirc_sq d)
        hv_n0 hv_n0 ⟨max d₁ d₀_ext, fun d hd => ?_⟩
      have hd_d1 : d₁ ≤ d := le_trans (le_max_left _ _) hd
      have hd_ext : d₀_ext ≤ d := le_trans (le_max_right _ _) hd
      have hd1 : 1 ≤ d := hd₁_pos.trans hd_d1
      let Pi₀ := keyLiftLaw F d fun desc key => liftInst S p Ac Cc (src.ham d desc key) (û d desc key)
      let Pi₁ := famLaw Fam (Nf d) d
      have hPi₀_valid := hKeyLift F d hd1 (fun desc key => liftInst S p Ac Cc (src.ham d desc key) (û d desc key))
      obtain ⟨hPi1_0, hPi1_sub, hPi1_zero, hPi1_l1⟩ := (hFam_hi d hd_d1).2
      let K_s : Inst (Nf d) → (Fin (k d) → Config S (Fin (Nf d))) → Option (Config S (Fin (Nf d))) → ℝ :=
        fun M X o => A.prob (tupleCode [encInst M, encSamples X]) (fun s => decConfig S (Nf d) s = o)
      let K_b : Inst (Nf d) → (Fin (D d) → Config S (Fin (Nf d))) → Option (Config S (Fin (Nf d))) → ℝ :=
        fun M X o => A'_ext.prob (tupleCode [encInst M, encSamples X]) (fun s => decConfig S (Nf d) s = o)
      have hshift : errExt S Pi₀ A (k d) - errExt S Pi₁ A (k d) ≤ 1 / (2 : ℝ) ^ d :=
        (hShiftExt S (Nf d) (k d) Pi₀ Pi₁ hPi₀_valid.1 hPi1_0 hPi1_sub hPi1_zero K_s
          (fun _ _ _ => p4c11d_ppt_prob_nonneg A _ _) (fun _ _ => p4c11d_ppt_fiber_sum_one A _ _)).trans hPi1_l1
      have hmix : 1 - errExt S Pi₀ A (k d) ≤ 2 * (D d : ℝ) * (1 - errExt S Pi₀ A'_ext (D d)) :=
        hPrefixExt S (Nf d) (k d) (D d) (hkD d) (hD1 d) Pi₀ hPi₀_valid.1 hPi₀_valid.2
          K_s (fun _ _ _ => p4c11d_ppt_prob_nonneg A _ _) (fun _ _ => p4c11d_ppt_fiber_sum_one A _ _)
          K_b (R_ext d) (hRe0 d) (hRe1 d) (w d) (hw_b d).1 (hw_b d).2 (hA'_ext_eq d)
      have hb72 : 1 - errExt S Pi₀ A'_ext (D d) ≤
          C₅₁ * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B_ext d +
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) +
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) + v₁ d + v₂ d := by
        linarith [hB_ext d hd_ext]
      have h1le2D : 1 ≤ 2 * (D d : ℝ) := by
        have : (1 : ℝ) ≤ (D d : ℝ) := by exact_mod_cast hD1 d
        linarith
      have hhalf_le : 1 / (2 : ℝ) ^ d ≤ 2 * (D d : ℝ) * (1 / (2 : ℝ) ^ d) :=
        le_mul_of_one_le_left (by positivity) h1le2D
      have hmul2D := mul_le_mul_of_nonneg_left hb72 (by positivity : 0 ≤ 2 * (D d : ℝ))
      linarith [hshift, hmix, hmul2D, hhalf_le]
    · refine hNegl Nf D T src.n0 v₁ v₂ (fun d => 1 - errAmp S (famLaw Fam (Nf d) d) A (k d))
        C₅₁ Cv hC₅₁ hCv.le F B_amp hCDH hNf_le hNf_poly hD_poly hT_poly (fun d => by rw [hn0_eq]; exact hcirc_sq d)
        hv_n0 hv_n0 ⟨max d₁ d₀_amp, fun d hd => ?_⟩
      have hd_d1 : d₁ ≤ d := le_trans (le_max_left _ _) hd
      have hd_amp : d₀_amp ≤ d := le_trans (le_max_right _ _) hd
      have hd1 : 1 ≤ d := hd₁_pos.trans hd_d1
      let Pi₀ := keyLiftLaw F d fun desc key => liftInst S p Ac Cc (src.ham d desc key) (û d desc key)
      let Pi₁ := famLaw Fam (Nf d) d
      have hPi₀_valid := hKeyLift F d hd1 (fun desc key => liftInst S p Ac Cc (src.ham d desc key) (û d desc key))
      obtain ⟨hPi1_0, hPi1_sub, hPi1_zero, hPi1_l1⟩ := (hFam_hi d hd_d1).2
      let K_s : Inst (Nf d) → (Fin (k d) → Config S (Fin (Nf d))) → Option (Fin (k d + 1) → Config S (Fin (Nf d))) → ℝ :=
        fun M X o => A.prob (tupleCode [encInst M, encSamples X]) (fun s => decTuple S (Nf d) (k d + 1) s = o)
      let K_b : Inst (Nf d) → (Fin (D d) → Config S (Fin (Nf d))) → Option (Fin (D d + 1) → Config S (Fin (Nf d))) → ℝ :=
        fun M X o => A'_amp.prob (tupleCode [encInst M, encSamples X]) (fun s => decTuple S (Nf d) (D d + 1) s = o)
      have hshift : errAmp S Pi₀ A (k d) - errAmp S Pi₁ A (k d) ≤ 1 / (2 : ℝ) ^ d :=
        (hShiftAmp S (Nf d) (k d) Pi₀ Pi₁ hPi₀_valid.1 hPi1_0 hPi1_sub hPi1_zero K_s
          (fun _ _ _ => p4c11d_ppt_prob_nonneg A _ _) (fun _ _ => p4c11d_ppt_fiber_sum_one A _ _)).trans hPi1_l1
      have hmix : 1 - errAmp S Pi₀ A (k d) ≤ 2 * (D d : ℝ) * (1 - errAmp S Pi₀ A'_amp (D d)) :=
        hPrefixAmp S (Nf d) (k d) (D d) (hkD d) (hD1 d) Pi₀ hPi₀_valid.1 hPi₀_valid.2
          K_s (fun _ _ _ => p4c11d_ppt_prob_nonneg A _ _) (fun _ _ => p4c11d_ppt_fiber_sum_one A _ _)
          K_b (R_amp d) (hRa0 d) (hRa1 d) (w d) (hw_b d).1 (hw_b d).2 (hA'_amp_eq d)
      have hb72 : 1 - errAmp S Pi₀ A'_amp (D d) ≤
          C₅₁ * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B_amp d +
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) +
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) + v₁ d + v₂ d := by
        linarith [hB_amp d hd_amp]
      have h1le2D : 1 ≤ 2 * (D d : ℝ) := by
        have : (1 : ℝ) ≤ (D d : ℝ) := by exact_mod_cast hD1 d
        linarith
      have hhalf_le : 1 / (2 : ℝ) ^ d ≤ 2 * (D d : ℝ) * (1 / (2 : ℝ) ^ d) :=
        le_mul_of_one_le_left (by positivity) h1le2D
      have hmul2D := mul_le_mul_of_nonneg_left hb72 (by positivity : 0 ≤ 2 * (D d : ℝ))
      linarith [hshift, hmix, hmul2D, hhalf_le]

end CritWinSpin

open CritWinSpin

theorem solution (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) (hP : ∀ (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
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
    (A : PPT), (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
      1 - C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errExt S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d)) ∧
    (∃ (B : PPT) (d₀ : ℕ), ∀ d ≥ d₀,
      1 - C * (T d : ℝ) * Real.sqrt (d : ℝ) * cdhAdv F B d -
          ((T d : ℝ) + ((T d).choose 2 : ℝ)) * (1 / (2 : ℝ) ^ d) -
          2 * (T d : ℝ) * Real.exp (-((src.n0 d : ℝ) ^ 2)) - v₁ d - v₂ d ≤
        errAmp S (keyLiftLaw F d fun desc key =>
          liftInst S p Ac Cc (src.ham d desc key) (û d desc key)) A (k d))) :
    (∃ Cρ : ℝ, 0 < Cρ ∧ ∀ ε : ℝ, 0 < ε → ε < dExp p → ∀ F : BilinearFamily, CDH F →
      ∃ (Fam : PPT) (Nf : ℕ → ℕ),
        (∀ d, d ≤ Nf d) ∧ PolyBounded Nf ∧
        (∀ d, 1 ≤ d → ∀ ω : Fin (Fam.coins.eval (unary d).length) → Bool,
          ∃ I : Inst (Nf d), Fam.alg (tupleCode [List.ofFn ω, unary d]) = encInst I ∧
            I.1.IsSymm ∧ I.2 = 0 ∧ (castM I.1).PosSemidef ∧
            ((tau S * (1 + (Nf d : ℝ) ^ (-dExp p + ε))) •
                (1 : Matrix (Fin (Nf d)) (Fin (Nf d)) ℝ) - castM I.1).PosSemidef ∧
            width (castM I.1) (castV I.2) ≤ Cρ) ∧
        ∀ (A : PPT) (k : ℕ → ℕ), (∀ d, 1 ≤ k d) → PolyBounded k →
          (∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
            1 - errExt S (famLaw Fam (Nf d) d) A (k d) ≤ 1 / (Nf d : ℝ) ^ c) ∧
          (∀ c : ℕ, ∃ d₀ : ℕ, ∀ d ≥ d₀,
            1 - errAmp S (famLaw Fam (Nf d) d) A (k d) ≤ 1 / (Nf d : ℝ) ^ c)) :=
  p4c_theorem_1_1_ii_decomp S p hS hp hP
