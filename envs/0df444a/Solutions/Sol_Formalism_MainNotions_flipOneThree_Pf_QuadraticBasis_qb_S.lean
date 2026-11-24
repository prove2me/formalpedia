-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis.qb_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:16.499619+00:00
-- url     : https://prove2.me/submissions/545c1ae1-97ee-4bc4-b6b5-f7af9c5455c9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_StatementO
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_QuadraticBasis_QuadBasis
import Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_QuadraticBasis_qb_I

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
variable {W O : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O]
namespace Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
theorem _root_.solution {p n' : ℕ} (hp : p.Prime) (j : W →+* O) (w θ : O) (hpW : Irreducible (p : W))
    (cW : Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ n') (hw2 : w ^ 2 = (p : O)) (hw : Irreducible w)
    (cO : Nat.card (O ⧸ Ideal.span {w}) = p ^ (2 * n')) (hθ : ∀ a : W, ¬ w ∣ θ - j a) (x : O) :
    ∃ (a b : W) (x' : O), x = j a + j b * θ + w * x' := by
  have hle : Ideal.span {(p : W)} ≤ Ideal.comap j (Ideal.span {w}) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hw2, Ideal.mem_span_singleton]
    exact dvd_pow_self w two_ne_zero
  let ι := Ideal.quotientMap (Ideal.span {w}) j hle
  let g : (W ⧸ Ideal.span {(p : W)}) × (W ⧸ Ideal.span {(p : W)}) → O ⧸ Ideal.span {w} :=
    fun t => ι t.1 + ι t.2 * Ideal.Quotient.mk _ θ
  have hg : ∀ a b : W, g (Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ b)
      = Ideal.Quotient.mk _ (j a + j b * θ) := by
    intro a b
    simp only [g, ι, Ideal.quotientMap_mk, map_add, map_mul]
  have hinj : Function.Injective g := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a'
    obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b'
    rw [hg, hg, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    have h2 : w ∣ j (a - a') + j (b - b') * θ := by
      have e : j (a - a') + j (b - b') * θ = j a + j b * θ - (j a' + j b' * θ) := by
        simp only [map_sub]; ring
      rwa [e]
    obtain ⟨h3, h4⟩ := qb_I j w θ hpW hw2 hw hθ h2
    have k3 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) a = Ideal.Quotient.mk _ a' :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h3)
    have k4 : (Ideal.Quotient.mk (Ideal.span {(p : W)})) b = Ideal.Quotient.mk _ b' :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 h4)
    rw [k3, k4]
  haveI : Finite (O ⧸ Ideal.span {w}) :=
    Nat.finite_of_card_ne_zero (by rw [cO]; exact (pow_pos hp.pos _).ne')
  have hbij := hinj.bijective_of_nat_card_le (by rw [Nat.card_prod, cW, cO, two_mul, pow_add])
  obtain ⟨⟨a, b⟩, hab⟩ := hbij.2 (Ideal.Quotient.mk _ x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [hg, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hab
  obtain ⟨x', hx'⟩ := hab
  exact ⟨a, b, x', by linear_combination hx'⟩
end Formalism.MainNotions.flipOneThree.Pf.QuadraticBasis
