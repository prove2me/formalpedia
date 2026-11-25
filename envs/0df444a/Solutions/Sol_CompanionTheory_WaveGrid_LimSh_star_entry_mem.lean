-- Prove2me | solution 1 for CompanionTheory.WaveGrid.LimSh.star_entry_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:46.791676+00:00
-- url     : https://prove2.me/submissions/62ab5e4f-df6a-4089-899e-43ffec5f861d

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting
import Definitions.Def_CompanionTheory_AutomorphicTheory_BesselWaveGrids_LettersPoly
import Theorems.Thm_Formalism_QuantumDeterminants_hpkFacts


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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) : (fun g : B.Mat k r => star (g i j)) ∈ Letters k r := by
  refine Submodule.subset_span (Or.inr ⟨fun a => Formalism.QuantumDeterminants.Hpk k r a i, star (Formalism.QuantumDeterminants.Hpk k r j), Or.inr ?_⟩)
  intro g hg
  have hH : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have hinv : g⁻¹ = Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), Matrix.mul_assoc (Formalism.QuantumDeterminants.Hpk k r), hg', hH]
  have e : Formalism.QuantumDeterminants.Hpk k r * (g⁻¹ * Formalism.QuantumDeterminants.Hpk k r) = gᴴ := by
    rw [hinv, Matrix.mul_assoc _ (Formalism.QuantumDeterminants.Hpk k r) (Formalism.QuantumDeterminants.Hpk k r), hH, Matrix.mul_one, ← Matrix.mul_assoc, hH,
      Matrix.one_mul]
  have e2 := congrFun (congrFun e j) i
  rw [conjTranspose_apply] at e2
  rw [star_star]
  exact e2.symm
end CompanionTheory.WaveGrid.LimSh
