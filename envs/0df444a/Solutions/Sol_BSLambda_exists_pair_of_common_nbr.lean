-- Prove2me | solution 1 for BSLambda.exists_pair_of_common_nbr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:15:07.072936+00:00
-- url     : https://prove2.me/submissions/9ef51b65-cd08-4bc8-b83a-1fa645fe84c4

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_CertFamily
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_GramClass
public import Theorems.Thm_BSLambda_exists_eq_flipSet_singleton_of_hammingDist_eq_one
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_singleton_flipSet_singleton
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution {x y z : Input V} (hxy : x ≠ y)
    (hxz : hammingDist x z = 1) (hyz : hammingDist y z = 1) :
    ∃ p q : V, p ≠ q ∧ y = flipSet x {p, q} := by
  obtain ⟨p, rfl⟩ := exists_eq_flipSet_singleton_of_hammingDist_eq_one hxz
  obtain ⟨q, hq⟩ := exists_eq_flipSet_singleton_of_hammingDist_eq_one hyz
  have hpq : p ≠ q := by
    rintro rfl
    exact hxy (flipSet_left_inj.mp hq)
  refine ⟨p, q, hpq, ?_⟩
  rw [← flipSet_singleton_flipSet_singleton x hpq, hq, flipSet_flipSet]
end BSLambda
