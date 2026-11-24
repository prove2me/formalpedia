-- Prove2me | solution 1 for Formalism.SLP.P.CountO.exists_hom_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:37:26.292081+00:00
-- url     : https://prove2.me/submissions/f7bfd629-5cf8-47bf-87a1-d22e2381752e

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace Formalism.SLP.P.CountO
theorem _root_.solution (P : Ideal R) [hPm : P.IsMaximal] [Finite (R ⧸ P)] {X : Type}
    [AddCommGroup X] [Module R X] (L : Submodule R X) (hPL : P • ⊤ ≤ L)
    (hL : L.toAddSubgroup.index = Nat.card (R ⧸ P)) :
    ∃ φ : X →ₗ[R] R ⧸ P, LinearMap.ker φ = L := by
  classical
  have hcardQ : Nat.card (X ⧸ L) = Nat.card (R ⧸ P) := hL
  have : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hPm.ne_top
  have hfin : Finite (X ⧸ L) :=
    Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact Nat.card_pos.ne')
  have hnt : Nontrivial (X ⧸ L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardQ]
    exact Finite.one_lt_card
  obtain ⟨v, hv⟩ := exists_ne (0 : X ⧸ L)
  let τ : R →ₗ[R] X ⧸ L := LinearMap.toSpanSingleton R (X ⧸ L) v
  have hker : P ≤ LinearMap.ker τ := by
    intro a ha
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L v
    simp only [LinearMap.mem_ker, τ, LinearMap.toSpanSingleton_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hPL (Submodule.smul_mem_smul ha Submodule.mem_top)
  let τ' : R ⧸ P →ₗ[R] X ⧸ L := Submodule.liftQ P τ hker
  have hinj : Function.Injective τ' := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P z
    rw [LinearMap.mem_ker] at hz
    have hz' : a • v = 0 := hz
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    by_contra ha
    obtain ⟨b, i, hi, hbi⟩ := Ideal.IsMaximal.exists_inv hPm ha
    have hiv : i • v = 0 := hker hi
    apply hv
    calc v = (b * a + i) • v := by rw [hbi, one_smul]
      _ = b • (a • v) + i • v := by rw [add_smul, mul_smul]
      _ = 0 := by rw [hz', hiv, smul_zero, add_zero]
  have hbij : Function.Bijective τ' :=
    hinj.bijective_of_nat_card_le (by rw [hcardQ])
  let e := LinearEquiv.ofBijective τ' hbij
  refine ⟨e.symm.toLinearMap ∘ₗ L.mkQ, ?_⟩
  rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]
end Formalism.SLP.P.CountO
