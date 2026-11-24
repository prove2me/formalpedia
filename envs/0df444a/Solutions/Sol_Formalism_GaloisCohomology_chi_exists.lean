-- Prove2me | solution 1 for Formalism.GaloisCohomology.chi_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:31.67639+00:00
-- url     : https://prove2.me/submissions/ad937f32-d616-4a8b-b5b8-ddca330ea31c

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_GaloisCohomology_GaloisCohomologyProofs_LdataNonempty
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
import Theorems.Thm_ReciprocityTheory_Gal_continuous_cycZ
import Theorems.Thm_ReciprocityTheory_Gal_cycZ_toZModPow_eq
import Theorems.Thm_ReciprocityTheory_Gal_unramOutside_iff
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
theorem _root_.solution (S : Set (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, ((l:ℕ) : 𝓞 F) ∉ v.asIdeal) :
    ∃ chi : GS Ω S →* ℤ_[l]ˣ, chi.comp (toGS Ω S) = cycZ F Ω l := by
  have hU : UnramOutside S (cycZ F Ω l) := by
    rw [unramOutside_iff S _ (continuous_cycZ F Ω l)]
    intro v hv A hA σ hσ
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq (hS v hv) hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  refine ⟨QuotientGroup.lift (NS Ω S) (cycZ F Ω l) (fun σ h => (MonoidHom.mem_ker).2 (hU σ h)), ?_⟩
  ext σ; rfl
end Formalism.GaloisCohomology
