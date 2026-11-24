-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.linearIndependent_tensor_D_of_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:42.858513+00:00
-- url     : https://prove2.me/submissions/a6e0a3f8-f82e-40fd-9105-a1a625dd2f49

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_LocalParameters
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_linearIndependent_tensor_D_of_ker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace FunctorialResolution.EmbeddedResolution
section
variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
  [Algebra k (IsLocalRing.ResidueField A)]
  [IsScalarTower k A (IsLocalRing.ResidueField A)]
  [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)] in
private theorem linearIndependent_tensor_D_of_ideal_eq_ker {ι : Type*} (I : Ideal A)
    (hI : I = RingHom.ker (algebraMap A (IsLocalRing.ResidueField A)))
    (m : ι → ↥I)
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) := by
  subst hI
  exact linearIndependent_tensor_D_of_ker k A m hm
end
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open scoped TensorProduct
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k A : Type*) [CommRing k] [CommRing A] [Algebra k A] [IsLocalRing A]
  [IsNoetherianRing A] [Algebra.FormallySmooth k A]
  [Module.Free A (KaehlerDifferential k A)] [Module.Finite A (KaehlerDifferential k A)]
  [Algebra k (IsLocalRing.ResidueField A)]
  [IsScalarTower k A (IsLocalRing.ResidueField A)]
  [Algebra.FormallySmooth k (IsLocalRing.ResidueField A)]
omit [IsNoetherianRing A] [Module.Free A (KaehlerDifferential k A)]
  [Module.Finite A (KaehlerDifferential k A)]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {ι : Type*}
    (m : ι → (IsLocalRing.maximalIdeal A : Ideal A))
    (hm : LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι => (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (m i))) :
    LinearIndependent (IsLocalRing.ResidueField A)
      (fun i : ι =>
        (1 : IsLocalRing.ResidueField A) ⊗ₜ[A] (KaehlerDifferential.D k A ((m i : A)))) :=
  linearIndependent_tensor_D_of_ideal_eq_ker k A (IsLocalRing.maximalIdeal A)
    (Ideal.mk_ker).symm m hm
end FunctorialResolution.EmbeddedResolution
