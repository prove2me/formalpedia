-- Prove2me | solution 1 for CompanionTheory.WaveGrid.LimSh.polyDeg_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:25:58.476362+00:00
-- url     : https://prove2.me/submissions/e14d6016-352a-4a48-9209-b3f3b39f05a0

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_LettersPoly
import Theorems.Thm_CompanionTheory_WaveGrid_LimSh_letters_pow_mono
import Theorems.Thm_CompanionTheory_WaveGrid_LimSh_mul_mem_letters_pow
import Theorems.Thm_CompanionTheory_WaveGrid_LimSh_entry_mem
import Theorems.Thm_CompanionTheory_WaveGrid_LimSh_star_entry_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.WaveGrid CompanionTheory.WaveGrid.LimSh
open Formalism.FourierDecayAlt Matrix CompanionTheory.LimBd.Main
variable {k r : ℕ}
namespace CompanionTheory.WaveGrid.LimSh
theorem _root_.solution {e : ℕ} {c : B.Mat k r → ℂ} (hc : U.IsPolyDeg e c) : c ∈ Letters k r ^ e := by
  classical
  obtain ⟨q, hq, hcq⟩ := hc
  let X : (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) ⊕ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) →
      B.Mat k r → ℂ := Sum.elim (fun x g => g x.1 x.2) (fun x g => star (g x.1 x.2))
  have hX : ∀ v, X v ∈ Letters k r := by
    rintro (x | x)
    · exact entry_mem x.1 x.2
    · exact star_entry_mem x.1 x.2
  have hpow : ∀ v (n : ℕ), X v ^ n ∈ Letters k r ^ n := fun v n => Submodule.pow_mem_pow _ (hX v) n
  have hprod : ∀ (m : _ →₀ ℕ) (s : Finset _), (∏ v ∈ s, X v ^ m v) ∈ Letters k r ^ (∑ v ∈ s, m v) := by
    intro m s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact mul_mem_letters_pow (hpow a _) ih
  have e1 : c = ∑ m ∈ q.support, q.coeff m • ∏ v ∈ m.support, X v ^ m v := by
    funext g
    rw [hcq g, MvPolynomial.eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.smul_apply, Finset.prod_apply, smul_eq_mul]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    rcases v with x | x <;> rfl
  rw [e1]
  refine Submodule.sum_mem _ fun m hm => Submodule.smul_mem _ _ (letters_pow_mono ?_ (hprod m m.support))
  exact (MvPolynomial.le_totalDegree hm).trans hq
end CompanionTheory.WaveGrid.LimSh
