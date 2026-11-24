-- Prove2me | solution 1 for Formalism.GaloisCohomology.ldata_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:54.270694+00:00
-- url     : https://prove2.me/submissions/f20de4d7-5e33-4c62-9a65-8ef8ea4369ab

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_GaloisCohomology_GaloisCohomologyProofs_LdataNonempty
import Theorems.Thm_Formalism_GaloisCohomology_chi_exists
import Theorems.Thm_Formalism_GaloisCohomology_above_finite
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_ReciprocityTheory_Gal_isPlaceOver_placeOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Representation ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open Formalism Formalism.GaloisCohomology
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  (l : ℕ) [Fact l.Prime]
namespace Formalism.GaloisCohomology
theorem _root_.solution : Nonempty (LData F Ω l) := by
  classical
  let S := (above_finite (F := F) l).toFinset
  have hS : (S : Set _) = Above F l := by simp [S]
  obtain ⟨chi, hchi⟩ := chi_exists (F := F) (Ω := Ω) l (S : Set _) (fun v hv h => hv (by rw [hS]; exact h))
  exact ⟨⟨S, hS, fun v => placeOf Ω v.1, fun v => isPlaceOver_placeOf Ω v.1, chi, hchi⟩⟩
end Formalism.GaloisCohomology
