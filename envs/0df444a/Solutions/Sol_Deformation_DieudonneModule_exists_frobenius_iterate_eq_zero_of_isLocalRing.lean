-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_frobenius_iterate_eq_zero_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/58f326fc-9d4e-5736-8fd0-74d7fc0d5769

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing

universe v

set_option autoImplicit false

namespace Deformation
p2m_export "Deformation" "wittHom counit_coeff_of_mem_wittHom wittHomFrobenius coeff_wittHomFrobenius DieudonneModule DieudonneModule.induction_on DieudonneModule.frobenius"
namespace DieudonneModule
p2m_export "Deformation.DieudonneModule" "of induction_on frobenius frobenius_of map"
namespace S4b
p2m_open "Deformation.DieudonneModule Deformation"

p2m_open "Deformation P2MW.S_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing.Deformation"

variable {p : ℕ} [hp : Fact p.Prime] {B : Type v} [CommRing B] [Bialgebra (ZMod p) B]

theorem coeff_wittHomFrobenius_iterate {k : ℕ} (x : wittHom (ZMod p) p k B) (n : ℕ) (i : Fin k) :
    (((wittHomFrobenius (ZMod p) p k B)^[n] x : wittHom (ZMod p) p k B) :
      TruncatedWittVector p k B).coeff i = ((x : TruncatedWittVector p k B).coeff i) ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', coeff_wittHomFrobenius, ih, ← pow_mul, ← pow_succ]

theorem frobenius_iterate_of {k : ℕ} (x : wittHom (ZMod p) p k B) (n : ℕ) :
    (frobenius (ZMod p) p B)^[n] (of (ZMod p) p B k x) =
      of (ZMod p) p B k ((wittHomFrobenius (ZMod p) p k B)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, frobenius_of]

theorem exists_pow_eq_zero_of_counit_eq_zero [Module.Finite (ZMod p) B] (hB : IsLocalRing B) :
    ∃ N : ℕ, ∀ b : B, Coalgebra.counit (R := ZMod p) b = 0 → b ^ N = 0 := by
  haveI := hB
  haveI : IsArtinianRing B := IsArtinianRing.of_finite (ZMod p) B
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hN
  refine ⟨N, fun b hb => ?_⟩
  have hmem : b ∈ IsLocalRing.maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h1 := hu.map (Bialgebra.counitAlgHom (ZMod p) B)
    have h2 : Bialgebra.counitAlgHom (ZMod p) B b = 0 := hb
    rw [h2] at h1
    exact not_isUnit_zero h1
  have : b ^ N ∈ (IsLocalRing.maximalIdeal B) ^ N := Ideal.pow_mem_pow hmem N
  rwa [hN, Ideal.zero_eq_bot, Ideal.mem_bot] at this

theorem main [Module.Finite (ZMod p) B] (hB : IsLocalRing B) :
    ∃ n : ℕ, ∀ z : DieudonneModule (ZMod p) p B, (frobenius (ZMod p) p B)^[n] z = 0 := by
  obtain ⟨N, hN⟩ := exists_pow_eq_zero_of_counit_eq_zero (p := p) hB
  refine ⟨N, fun z => ?_⟩
  induction z using DieudonneModule.induction_on with
  | ih k x =>
    rw [frobenius_iterate_of]
    have : (wittHomFrobenius (ZMod p) p k B)^[N] x = 0 := by
      refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
      rw [coeff_wittHomFrobenius_iterate, ZeroMemClass.coe_zero, TruncatedWittVector.coeff_zero]
      exact pow_eq_zero_of_le (Nat.lt_pow_self hp.out.one_lt).le
        (hN _ (counit_coeff_of_mem_wittHom x.2 i))
    rw [this, map_zero]

end Deformation.DieudonneModule.S4b

theorem solution
    (p : ℕ) [Fact p.Prime] (B : Type v) [CommRing B] [Bialgebra (ZMod p) B] [Module.Finite (ZMod p) B]
    (hB : IsLocalRing B) :
    ∃ n : ℕ, ∀ z : Deformation.DieudonneModule (ZMod p) p B,
      (Deformation.DieudonneModule.frobenius (ZMod p) p B)^[n] z = 0 :=
  Deformation.DieudonneModule.S4b.main hB

end S_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_frobenius_iterate_eq_zero_of_isLocalRing (solution)
