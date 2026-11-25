-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf.chain_bound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:39:14.407524+00:00
-- url     : https://prove2.me/submissions/bce994f1-4191-4c09-993c-61dd039a48be

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChain
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJABddSSnChainPf
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_ChainPf_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_ge_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {V E' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
theorem _root_.solution : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainBd := by
  unfold Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainBd
  intro k r V E' _ _ _ _ _ Ψ hΨ F U K hU hF hKU hKG Bg hBg hyp m
  classical
  obtain ⟨C0, hC0⟩ := hyp 0
  have hFb : ∀ g ∈ K, ‖F g‖ ≤ C0 := by
    intro g hg
    have := hC0 [] [] (by simp) (by simp) (by simp) g hg
    simpa [dLR, Rw] using this
  have hΨb : ∀ j : ℕ, ∃ B, ∀ y : V, ‖y‖ ≤ C0 → ‖iteratedFDeriv ℝ j Ψ y‖ ≤ B := by
    intro j
    have hc : Continuous (fun y => iteratedFDeriv ℝ j Ψ y) :=
      hΨ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) C0).exists_bound_of_continuousOn hc.continuousOn
    exact ⟨B, fun y hy => hB y (mem_closedBall_zero_iff.mpr hy)⟩
  choose Bj hBj using hΨb
  choose Cl hCl using hyp
  obtain ⟨Bs, hBs⟩ : ∃ Bs : ℝ, Bs = ∑ j ∈ Finset.range (m + 1), |Bj j| := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs : ℝ, Cs = 1 + ∑ l ∈ Finset.range (m + 1), |Cl l| := ⟨_, rfl⟩
  have hBs0 : 0 ≤ Bs := by
    rw [hBs]
    exact Finset.sum_nonneg fun j _ => abs_nonneg _
  have hCs1 : 1 ≤ Cs := by
    have := Finset.sum_nonneg (fun l (_ : l ∈ Finset.range (m + 1)) => abs_nonneg (Cl l))
    rw [hCs]
    linarith
  have hBj' : ∀ j ≤ m, Bj j ≤ Bs := by
    intro j hj
    rw [hBs]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Bj j|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega)))
  have hCl' : ∀ l ≤ m, Cl l ≤ Cs := by
    intro l hl
    have := (le_abs_self (Cl l)).trans (Finset.single_le_sum (f := fun l => |Cl l|) (fun l _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega : l < m + 1)))
    rw [hCs]
    linarith
  refine ⟨(m + 1).factorial * Bs * Cs ^ m, ?_⟩
  intro u v hu hv huv g hg
  have hgG := hKG hg
  have hg1 : 1 ≤ gN g := gN_ge_one hgG
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = gN g ^ Bg := ⟨_, rfl⟩
  have ha1 : 1 ≤ a := by
    rw [ha]
    exact Real.one_le_rpow hg1 hBg
  have hpow : ∀ l : ℕ, gN g ^ (Bg * l) = a ^ l := by
    intro l
    rw [Real.rpow_mul (by linarith), Real.rpow_natCast, ha]
  have hsub : ∀ s : List (Bool × Mat k r), s.Sublist (wL u ++ wR v) → ‖Dw s F g‖ ≤ Cs * a ^ s.length := by
    intro s hs
    unfold wL wR at hs
    obtain ⟨r1, r2, rfl, h1, h2⟩ := List.sublist_append_iff.mp hs
    obtain ⟨u', hu', rfl⟩ := List.sublist_map_iff.mp h1
    obtain ⟨v', hv', rfl⟩ := List.sublist_map_iff.mp h2
    have hl : u'.length + v'.length ≤ m := by
      have := hu'.length_le
      have := hv'.length_le
      omega
    have e : Dw (u'.map (Prod.mk true) ++ v'.map (Prod.mk false)) F g = dLR u' v' F g := by
      rw [dLR_eq]
      rfl
    rw [e]
    have hb := hCl (u'.length + v'.length) u' v' (fun X hX => hu X (hu'.subset hX))
      (fun X hX => hv X (hv'.subset hX)) le_rfl g hg
    rw [hpow] at hb
    have hlen : (u'.map (Prod.mk true) ++ v'.map (Prod.mk false)).length = u'.length + v'.length := by simp
    rw [hlen]
    calc ‖dLR u' v' F g‖ ≤ Cl (u'.length + v'.length) * a ^ (u'.length + v'.length) := hb
      _ ≤ Cs * a ^ (u'.length + v'.length) :=
        mul_le_mul_of_nonneg_right (hCl' _ hl) (pow_nonneg (by linarith) _)
  rw [dLR_eq]
  have hw : ∀ y ∈ wL u ++ wR v, inLie k r y.2 := by
    intro y hy
    simp only [wL, wR, List.mem_append, List.mem_map] at hy
    rcases hy with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hu X hX).1
    · exact (hv X hX).1
  obtain ⟨ts, hlen, hts, hval⟩ := expand hΨ hU hF (wL u ++ wR v) hw
  rw [hval g (hKU hg) hgG]
  have hL : (wL u ++ wR v).length ≤ m := by
    simp only [wL, wR, List.length_append, List.length_map]
    omega
  have hX : 0 ≤ Bs * Cs ^ m * gN g ^ (Bg * m) :=
    mul_nonneg (mul_nonneg hBs0 (pow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _)
  have hterm : ∀ t ∈ ts, ‖tval Ψ F t g‖ ≤ Bs * Cs ^ m * gN g ^ (Bg * m) := by
    intro t ht
    obtain ⟨hj, hsum, hsl⟩ := hts t ht
    rw [hpow]
    unfold tval
    calc ‖iteratedFDeriv ℝ t.j Ψ (F g) (fun i => Dw (t.ws i) F g)‖
        ≤ ‖iteratedFDeriv ℝ t.j Ψ (F g)‖ * ∏ i, ‖Dw (t.ws i) F g‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ Bs * ∏ i, (Cs * a ^ (t.ws i).length) := by
          apply mul_le_mul ((hBj t.j (F g) (hFb g hg)).trans (hBj' _ (by omega)))
            (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hsub _ (hsl i)))
            (Finset.prod_nonneg fun i _ => norm_nonneg _) hBs0
      _ = Bs * (Cs ^ t.j * a ^ (wL u ++ wR v).length) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_pow_eq_pow_sum, hsum]
      _ ≤ Bs * (Cs ^ m * a ^ m) := by
          apply mul_le_mul_of_nonneg_left _ hBs0
          exact mul_le_mul (pow_le_pow_right₀ hCs1 (by omega)) (pow_le_pow_right₀ ha1 hL)
            (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)
      _ = Bs * Cs ^ m * a ^ m := by ring
  have key : ∀ l : List (Tm k r), (∀ t ∈ l, ‖tval Ψ F t g‖ ≤ Bs * Cs ^ m * gN g ^ (Bg * m)) →
      ‖(l.map fun t => tval Ψ F t g).sum‖ ≤ l.length * (Bs * Cs ^ m * gN g ^ (Bg * m)) := by
    intro l
    induction l with
    | nil =>
      intro _
      simp
    | cons t l ih =>
      intro hl
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      calc _ ≤ ‖tval Ψ F t g‖ + ‖(l.map fun t => tval Ψ F t g).sum‖ := norm_add_le _ _
        _ ≤ (Bs * Cs ^ m * gN g ^ (Bg * m)) + l.length * (Bs * Cs ^ m * gN g ^ (Bg * m)) :=
          add_le_add (hl t (by simp)) (ih fun t' ht' => hl t' (by simp [ht']))
        _ = _ := by ring
  have hfac : (ts.length : ℝ) ≤ ((m + 1).factorial : ℝ) := by
    exact_mod_cast hlen.trans (Nat.factorial_le (by omega))
  calc ‖(ts.map fun t => tval Ψ F t g).sum‖ ≤ ts.length * (Bs * Cs ^ m * gN g ^ (Bg * m)) := key ts hterm
    _ ≤ ((m + 1).factorial : ℝ) * (Bs * Cs ^ m * gN g ^ (Bg * m)) := mul_le_mul_of_nonneg_right hfac hX
    _ = _ := by ring
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.ChainPf
