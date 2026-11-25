-- Prove2me | solution 1 for CompanionTheory.Bmu.absBound_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:16:08.90487+00:00
-- url     : https://prove2.me/submissions/71d0920b-7589-4da7-af54-9ad56bc7c0cf

import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ContinuousOnOrbit
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselOrbitBounds_BesselMapUniqueness_ProdNormLe
import Theorems.Thm_CompanionTheory_Bmu_prod_norm_le
import Theorems.Thm_CompanionTheory_Bmu_CWLin_zero
import Theorems.Thm_CompanionTheory_Bmu_LieWd_lieW
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate
noncomputable section
open CompanionTheory CompanionTheory.Bmu
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace CompanionTheory.Bmu
theorem _root_.solution (hF : Factor) (hAd : DsAd) (hDer : DsDer) (hWB : WordBd) : AbsBound := by
  intro n Hm H _ _ _ σ hU V _ _ _ B hB e Q hQ C m hC hQB C₀ c w hw
  obtain ⟨N, Wd, β, hWd, hβ⟩ := hF n Hm H σ hU V B hB
  obtain ⟨Cw, hCw, hW⟩ := hWB n Hm H σ hU w hw (m + c * m)
  set A : ℝ := max 1 C₀ with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  refine ⟨C * (Cw * A ^ (m + c * m)), fun g hg M hM hconj hcase => ?_⟩
  have hMc : 1 ≤ M ^ c := one_le_pow₀ hM

  have main : ∀ R : List (Mat n), LieWd Hm R → R.length ≤ c * m → (∀ X ∈ R, ‖X‖ ≤ A) →
      ‖B (σ g (dsW σ R w))‖ ≤ C * (Cw * A ^ (m + c * m) * M ^ (c * m)) := by
    intro R hR hRl hRn
    have hu : IsSm (UH Hm) σ (dsW σ R w) := hw.dsW hU.rep hR.lieW
    refine hQB _ (hu.apply hU.rep hg) _ fun P hP => ?_
    have hPL : LieWd Hm (P.map Q) := fun X hX => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hX; exact hQ i
    obtain ⟨h1, h2⟩ := hAd n Hm H σ hU g hg _ hPL
    rw [h2 _ hu, hU.iso g hg]
    set P' := (P.map Q).map fun X => g⁻¹ * X * g with hP'
    have hl : P'.length = P.length := by simp [hP']
    have e1 : dsW σ P' (dsW σ R w) = dsW σ (P' ++ R) w := by unfold dsW; rw [List.foldr_append]
    rw [e1]
    refine (hW (P' ++ R) (fun X hX => (List.mem_append.1 hX).elim (h1 X) (hR X))
      (by rw [List.length_append, hl]; omega)).trans ?_
    rw [List.map_append, List.prod_append, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hCw
    have b1 : (P'.map fun X => ‖X‖).prod ≤ (A * M ^ c) ^ m := by
      refine (prod_norm_le P' (a := A * M ^ c) fun X hX => ?_).trans ?_
      · obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hY
        exact (hconj i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      · exact pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hA1 hMc) (hl ▸ hP)
    have b2 : (R.map fun X => ‖X‖).prod ≤ A ^ (c * m) := (prod_norm_le R hRn).trans (pow_le_pow_right₀ hA1 hRl)
    have h0 : 0 ≤ (R.map fun X => ‖X‖).prod := List.prod_nonneg fun x hx => by
      obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    calc _ ≤ (A * M ^ c) ^ m * A ^ (c * m) := mul_le_mul b1 b2 h0 (by positivity)
      _ = A ^ (m + c * m) * M ^ (c * m) := by rw [mul_pow, ← pow_mul, pow_add]; ring
  rcases hcase with h1 | ⟨Y, lam, hY, hYn, hlam, hχ⟩
  · have := main [] (fun _ h => absurd h List.not_mem_nil) (Nat.zero_le _) (fun _ h => absurd h List.not_mem_nil)
    rw [h1, one_pow, mul_one] at this
    exact this
  · have step : ∀ u, IsSm (UH Hm) σ u → B (σ g (ds σ Y u)) = (Complex.I * lam) • B (σ g u) := by
      intro u hu
      have hds : IsSm (UH Hm) σ (ds σ Y u) :=
        hu.dsW hU.rep (W := [Y]) (LieWd.lieW fun X hX => by rw [List.mem_singleton.1 hX]; exact hY)
      have d1 : HasDerivAt (fun τ : ℝ => ∑ i, β i (dsW σ (Wd i) (σ (g * ex Y τ) u)))
          (∑ i, β i (dsW σ (Wd i) (σ g (ds σ Y u)))) 0 :=
        HasDerivAt.fun_sum fun i _ => ((β i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
          (hDer n Hm H σ hU _ (hWd i) g hg Y hY u hu)
      have e1 : (fun τ : ℝ => ∑ i, β i (dsW σ (Wd i) (σ (g * ex Y τ) u))) =
          fun τ : ℝ => Complex.exp (Complex.I * (lam * τ : ℝ)) • B (σ g u) := by
        funext τ
        rw [← hβ _ (hu.apply hU.rep (hU.rep.mul_mem _ hg _ (ex_mem_of_lie hY τ))), hχ τ u hu]
      have d2 : HasDerivAt (fun τ : ℝ => Complex.exp (Complex.I * (lam * τ : ℝ))) (Complex.I * lam) 0 := by
        have h1 : HasDerivAt (fun τ : ℝ => Complex.I * ((lam * τ : ℝ) : ℂ)) (Complex.I * lam) 0 := by
          have := (((hasDerivAt_id (0 : ℝ)).const_mul lam).ofReal_comp).const_mul Complex.I
          simpa using this
        simpa using h1.cexp
      rw [e1, ← hβ _ (hds.apply hU.rep hg)] at d1
      exact d1.unique (d2.smul_const _)
    have iter : ∀ j : ℕ, B (σ g (dsW σ (List.replicate j Y) w)) = (Complex.I * lam) ^ j • B (σ g w) := by
      intro j
      induction j with
      | zero => simp [dsW]
      | succ j ih =>
        have hu : IsSm (UH Hm) σ (dsW σ (List.replicate j Y) w) :=
          hw.dsW hU.rep (LieWd.lieW fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hY)
        rw [List.replicate_succ, dsW_cons, step _ hu, ih, smul_smul, pow_succ']
    have h := main (List.replicate (c * m) Y) (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hY)
      (by simp) (fun X hX => by rw [List.eq_of_mem_replicate hX]; exact hYn.trans (le_max_right _ _))
    rw [iter, norm_smul, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs] at h
    have hMp : 0 < M ^ (c * m) := by positivity
    have h2 : M ^ (c * m) * ‖B (σ g w)‖ ≤ |lam| ^ (c * m) * ‖B (σ g w)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith) hlam _) (norm_nonneg _)
    refine le_of_mul_le_mul_left (h2.trans (h.trans_eq ?_)) hMp
    ring
end CompanionTheory.Bmu
