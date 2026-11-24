-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.exists_max_above
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:12.742427+00:00
-- url     : https://prove2.me/submissions/f8ff5666-efbf-49a8-8f12-6f9622c3ac6f

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution (E : Type) [Field E] [NumberField E] (I : Ideal (𝓞 E)) (p : ℕ) (hp : p.Prime)
    (hI : p ∣ Ideal.absNorm I) (h0 : Ideal.absNorm I ≠ 0) :
    ∃ P : Ideal (𝓞 E), P.IsMaximal ∧ I ≤ P ∧ ((p : ℕ) : 𝓞 E) ∈ P := by
  have hcard : Ideal.absNorm I = Nat.card (𝓞 E ⧸ I) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (𝓞 E ⧸ I) := Nat.finite_of_card_ne_zero (hcard ▸ h0)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ I) p (hcard ▸ hI)
  have hne : I ⊔ Ideal.span {((p : ℕ) : 𝓞 E)} ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 E) ∈ I ⊔ Ideal.span {((p : ℕ) : 𝓞 E)} := by rw [htop]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hb
    have hpx : p • x = 0 := hx ▸ addOrderOf_nsmul_eq_zero x
    have h2 : (Ideal.Quotient.mk I (c * (p : 𝓞 E))) = 1 := by
      rw [← map_one (Ideal.Quotient.mk I), ← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    have h3 : x = 0 := by
      calc x = 1 * x := (one_mul x).symm
        _ = Ideal.Quotient.mk I c * (p • x) := by
            rw [← h2, map_mul, map_natCast, nsmul_eq_mul, mul_assoc]
        _ = 0 := by rw [hpx, mul_zero]
    rw [h3, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨P, hP, le_sup_left.trans hle,
    hle (Submodule.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
