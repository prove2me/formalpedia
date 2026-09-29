-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/10bd0324-e0b3-5275-9605-4b3d1030c8db

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
import Theorems.Thm_CerednikDrinfeld_exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic
import Theorems.Thm_CerednikDrinfeld_exists_monoidHom_generalLinearGroup_eq_ofAdd_iff_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule

namespace R4IsoCrit

variable {r : ℕ} [hr : Fact r.Prime]

section Witt

variable (k : Type) [Field k] [CharP k r] [IsAlgClosed k]

theorem isField_quot : IsField (WittVector r k ⧸ pIdeal r (WittVector r k)) :=
  MulEquiv.isField (Field.toIsField k) (WittVector.quotientPEquiv (p := r) (k := k)).toMulEquiv

omit [IsAlgClosed k] in
theorem charP_quot : CharP (WittVector r k ⧸ pIdeal r (WittVector r k)) r := by
  refine CharP.quotient (WittVector r k) r ?_
  intro hu
  have h0 : WittVector.constantCoeff ((r : ℕ) : WittVector r k) = 0 := by
    rw [map_natCast, CharP.cast_eq_zero]
  exact not_isUnit_zero (h0 ▸ hu.map (WittVector.constantCoeff : WittVector r k →+* k))

end Witt

theorem ofAdd_pow (v c : ℤ) : (Multiplicative.ofAdd v) ^ c = Multiplicative.ofAdd (c * v) := by
  rw [← ofAdd_zsmul, smul_eq_mul]

theorem nu_eq_two_mul
    (vdet ν : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) =
        algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)
    (c : ℤ) (hc : ∀ g, ν g = (vdet g) ^ c)
    (h4 : ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r],
      (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = (r : ℚ_[r]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r]) →
        ν g = Multiplicative.ofAdd (4 : ℤ))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) :
    ν g = Multiplicative.ofAdd (2 * Multiplicative.toAdd (vdet g)) := by
  have hdet : ((r : ℚ_[r]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r])).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hr.out.ne_zero)
  set gr := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hgr
  have hgr_coe : (gr : Matrix (Fin 2) (Fin 2) ℚ_[r]) = (r : ℚ_[r]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r]) :=
    rfl
  have hv2 : vdet gr = Multiplicative.ofAdd 2 := by
    refine (hvdet gr 2).2 ⟨1, ?_⟩
    rw [Matrix.GeneralLinearGroup.val_det_apply, hgr_coe, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin, Units.val_one, map_one, one_mul, map_natCast, zpow_ofNat]
  have hc2 : c = 2 := by
    have := h4 gr hgr_coe
    rw [hc, hv2, ofAdd_pow] at this
    have h' : c * 2 = 4 := Multiplicative.ofAdd.injective this
    omega
  rw [hc g, hc2]
  conv_lhs => rw [show vdet g = Multiplicative.ofAdd (Multiplicative.toAdd (vdet g)) from rfl]
  rw [ofAdd_pow]

theorem main (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r (WittVector r k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hE : Function.Injective E ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r])))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e) :
    ∃ m' : ℕ, FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) := by

  letI : Field (WittVector r k ⧸ pIdeal r (WittVector r k)) := (isField_quot k).toField
  haveI : CharP (WittVector r k ⧸ pIdeal r (WittVector r k)) r := charP_quot k
  obtain ⟨ν, hν4, hν⟩ :=
    CerednikDrinfeld.FormalODModule.exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
      (WittVector r k ⧸ pIdeal r (WittVector r k)) Φ hΦ4 E hE
  obtain ⟨h, hνg, hfin, hfib⟩ := hν e g hg

  obtain ⟨vdet, hvdet⟩ :=
    CerednikDrinfeld.exists_monoidHom_generalLinearGroup_eq_ofAdd_iff_of_irreducible ℤ_[r] inferInstance
      (r : ℤ_[r]) PadicInt.irreducible_p ℚ_[r] (Fin 2)
  obtain ⟨c, hc⟩ :=
    CerednikDrinfeld.exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic vdet hvdet ν
  have hνg' := nu_eq_two_mul vdet ν hvdet c hc hν4 g
  rw [hνg] at hνg'
  have h2 : (h : ℤ) = 2 * Multiplicative.toAdd (vdet g) := Multiplicative.ofAdd.injective hνg'
  refine ⟨(Multiplicative.toAdd (vdet g)).toNat, ?_⟩
  have hh : h = 2 * (Multiplicative.toAdd (vdet g)).toNat := by omega

  haveI : Module.Free (WittVector r k ⧸ pIdeal r (WittVector r k))
      (KerAlgebra (e : MvFormalGroup.End Φ.F).toPowerSeries) := Module.Free.of_divisionRing _ _
  refine ⟨hfin, Module.Projective.of_free, fun κ _ f => ?_⟩
  rw [← hh]
  exact hfib κ f

end R4IsoCrit

end

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r (WittVector r k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hE : Function.Injective E ∧
      ∃ m : ℕ,
        (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
        (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r])))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e) :
    ∃ m' : ℕ, FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) :=
  R4IsoCrit.main k ι Φ hΦ hΦ4 E hE e g hg

end S_CerednikDrinfeld_SpecialFormal_exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq (solution)
