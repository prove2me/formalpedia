-- Prove2me | solution 1 for Formalism.L2.SG.Pf.SatGramLoc.image_places_primesOver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:20.958088+00:00
-- url     : https://prove2.me/submissions/46ef55a7-83ef-4760-99a7-64bce0fbe1fd

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLoc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_SatGramLocPfA
import Theorems.Thm_Formalism_L2_SG_Pf_SatGramLoc_liesOver_natCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.SatGramLoc
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.SG.Pf.SatGramLoc
theorem _root_.solution (p : ℕ) (hp : p.Prime) :
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) '' {v | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal} =
      (Ideal.span {(p : ℤ)}).primesOver (𝓞 K) := by
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.isPrime, liesOver_natCast p hp v hv⟩
  · rintro ⟨hP, hPo⟩
    have h' : (p : ℤ) ∈ Ideal.span {(p : ℤ)} := Ideal.subset_span rfl
    rw [hPo.over] at h'
    have h'' : algebraMap ℤ (𝓞 K) (p : ℤ) ∈ P := h'
    have hmem : ((p : ℕ) : 𝓞 K) ∈ P := by simpa using h''
    have hne : P ≠ ⊥ := by
      intro h
      rw [h, Ideal.mem_bot] at hmem
      exact hp.ne_zero (by exact_mod_cast hmem)
    exact ⟨⟨P, hP, hne⟩, hmem, rfl⟩
end Formalism.L2.SG.Pf.SatGramLoc
