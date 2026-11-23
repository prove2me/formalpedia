-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.DD_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:40.147141+00:00
-- url     : https://prove2.me/submissions/f398cbb3-392c-423f-9499-f664f59e3e43

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pa_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pa_erase
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_fac_dvd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_pa_dvd
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_DD_eval_a
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_DD_eval_b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (s : Finset ℕ) (ρ : ℕ → ℂ) (hinj : ∀ i ∈ s, ∀ j ∈ s, ρ i = ρ j → i = j)
    (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ)
    (H1 : ∀ l ∈ s, c * q1.eval (-ρ l) +
      M l * ((∏ j ∈ s.erase l, (-ρ l + ρ j)) * ∏ j ∈ s, (-ρ l + (ρ j + 1))) = 0)
    (H2 : ∀ l ∈ s, c * q1.eval (-(ρ l + 1)) -
      N l * ((∏ j ∈ s, (-(ρ l + 1) + ρ j)) * ∏ j ∈ s.erase l, (-(ρ l + 1) + (ρ j + 1))) = 0)
    (H3 : ∀ l ∈ s, ∀ m ∈ s, ρ m = ρ l + 1 →
      N l = 0 ∧ M m = 0 ∧ (X + C (ρ l + 1)) * (X + C (ρ l + 1)) ∣ q1) :
    pa s ρ * pa s (fun i => ρ i + 1) ∣ DD s ρ c q1 N M := by
  obtain ⟨D1, hD1⟩ := pa_dvd s ρ hinj (DD s ρ c q1 N M)
    (fun l hl => by rw [DD_eval_a _ _ _ _ _ _ l hl]; exact H1 l hl)
  have key : pa s (fun i => ρ i + 1) ∣ D1 := by
    apply pa_dvd s (fun i => ρ i + 1) (fun i hi j hj h => hinj i hi j hj (add_right_cancel h))
    intro l hl
    show D1.eval (-(ρ l + 1)) = 0
    have hD0 : (DD s ρ c q1 N M).eval (-(ρ l + 1)) = 0 := by
      rw [DD_eval_b _ _ _ _ _ _ l hl]; exact H2 l hl
    by_cases hdeg : ∃ m ∈ s, ρ m = ρ l + 1
    · obtain ⟨m, hm, hml⟩ := hdeg
      obtain ⟨hN, hM, hq⟩ := H3 l hl m hm hml
      have ht0 : (X + C (ρ l + 1) : ℂ[X]) ≠ 0 := (monic_X_add_C _).ne_zero
      have hta : ∀ s' : Finset ℕ, m ∈ s' → (X + C (ρ l + 1) : ℂ[X]) ∣ pa s' ρ := by
        intro s' h; have := fac_dvd s' ρ m h; rwa [hml] at this
      have htb : ∀ s' : Finset ℕ, l ∈ s' → (X + C (ρ l + 1) : ℂ[X]) ∣ pa s' (fun i => ρ i + 1) :=
        fun s' h => fac_dvd s' (fun i => ρ i + 1) l h
      have htt : (X + C (ρ l + 1) : ℂ[X]) * (X + C (ρ l + 1)) ∣ DD s ρ c q1 N M := by
        unfold DD
        refine dvd_sub (dvd_add (Dvd.dvd.mul_left hq _) (Finset.dvd_sum ?_)) (Finset.dvd_sum ?_)
        · intro j hj
          by_cases hjm : j = m
          · rw [hjm, hM]; simp
          · exact Dvd.dvd.mul_left (mul_dvd_mul (hta _ (Finset.mem_erase.2 ⟨fun h => hjm h.symm, hm⟩)) (htb _ hl)) _
        · intro j hj
          by_cases hjl : j = l
          · rw [hjl, hN]; simp
          · exact Dvd.dvd.mul_left (mul_dvd_mul (hta _ hm) (htb _ (Finset.mem_erase.2 ⟨fun h => hjl h.symm, hl⟩))) _
      have hpa : pa s ρ = (X + C (ρ l + 1)) * pa (s.erase m) ρ := by rw [pa_erase s ρ m hm, hml]
      rw [hD1, hpa, mul_assoc] at htt
      have h3 : (X + C (ρ l + 1) : ℂ[X]) ∣ pa (s.erase m) ρ * D1 := (mul_dvd_mul_iff_left ht0).1 htt
      have e : (X + C (ρ l + 1) : ℂ[X]) = X - C (-(ρ l + 1)) := by rw [C_neg, sub_neg_eq_add]
      rw [e, dvd_iff_isRoot, IsRoot.def, eval_mul, pa_eval] at h3
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h4
        obtain ⟨j, hj, hj0⟩ := h4
        have : ρ j = ρ m := by rw [hml]; linear_combination hj0
        exact (Finset.mem_erase.1 hj).1 (hinj j (Finset.mem_erase.1 hj).2 m hm this)
      · exact h4
    · have hdeg : ∀ j ∈ s, ρ j ≠ ρ l + 1 := fun j hj h => hdeg ⟨j, hj, h⟩
      rw [hD1, eval_mul, pa_eval] at hD0
      rcases mul_eq_zero.1 hD0 with h4 | h4
      · exfalso
        rw [Finset.prod_eq_zero_iff] at h4
        obtain ⟨j, hj, hj0⟩ := h4
        exact hdeg j hj (by linear_combination hj0)
      · exact h4
  rw [hD1]
  exact mul_dvd_mul_left _ key
end Formalism.FourierDecayAlt.P.Mx7
