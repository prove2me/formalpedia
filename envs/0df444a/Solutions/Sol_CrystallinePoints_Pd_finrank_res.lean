-- Prove2me | solution 1 for CrystallinePoints.Pd.finrank_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:32:26.472473+00:00
-- url     : https://prove2.me/submissions/20c9d60c-4205-4ff4-b71e-37f92a98bcb5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_PoincareDeRhamDuality_DeRhamPerfectPairing_ResSurjD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open TensorProduct
open CrystallinePoints CrystallinePoints.Pd
namespace CrystallinePoints.Pd
theorem _root_.solution {R : Type} [CommRing R] (m : Ideal R) [hm : m.IsMaximal] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] :
    Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = Module.rankAtStalk M (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := by
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  have h := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ m) (⊥ : PrimeSpectrum (R ⧸ m))
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  rw [show Module.finrank (R ⧸ m) ((R ⧸ m) ⊗[R] M) = _ from h]
  congr 1
  ext x
  simp [Ideal.Quotient.eq_zero_iff_mem]
end CrystallinePoints.Pd
