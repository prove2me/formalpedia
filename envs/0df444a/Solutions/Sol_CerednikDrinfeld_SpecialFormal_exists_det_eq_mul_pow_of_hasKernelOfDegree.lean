-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.exists_det_eq_mul_pow_of_hasKernelOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/54c965e0-d205-5979-ad75-07a7e75c8e86

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
import Theorems.Thm_CerednikDrinfeld_exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic
import Theorems.Thm_CerednikDrinfeld_exists_monoidHom_generalLinearGroup_eq_ofAdd_iff_of_irreducible
import Theorems.Thm_MvPowerSeries_finite_flat_exists_basis_substAlgHom_of_finite_quotient
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_exists_det_eq_mul_pow_of_hasKernelOfDegree
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open MvPowerSeries
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule

namespace R4DetHeight

section Witt

variable {r : ℕ} [hr : Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]

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

section Invertible

variable {r : ℕ} [hr : Fact r.Prime] {K : Type u} [Field K]
variable {Φ : FormalODModule r K}

abbrev Λ (Φ : FormalODModule r K) : Subring (MvFormalGroup.End Φ.F) :=
  Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})

abbrev ser (e : Λ Φ) : Series K := (e : MvFormalGroup.End Φ.F).toPowerSeries

theorem ser_constantCoeff (e : Λ Φ) (i : Fin 2) : constantCoeff (ser e i) = 0 :=
  (e : MvFormalGroup.End Φ.F).constantCoeff_eq_zero i

theorem ser_mul (e e' : Λ Φ) : ser (e * e') = fun i => subst (ser e') (ser e i) := rfl

theorem ser_zero : ser (0 : Λ Φ) = fun _ => 0 := rfl

theorem eq_zero_of_ser (e : Λ Φ) (h : ∀ i, ser e i = 0) : e = 0 := by
  have h1 : (e : MvFormalGroup.End Φ.F) = 0 := MvFormalGroup.Hom.ext (funext h)
  exact_mod_cast h1

theorem span_ser_ne_top (e : Λ Φ) : Ideal.span (Set.range (ser e)) ≠ ⊤ := by
  intro htop
  have hle : Ideal.span (Set.range (ser e)) ≤
      RingHom.ker (constantCoeff : MvPowerSeries (Fin 2) K →+* K) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact ser_constantCoeff e i
  have h1 : (1 : MvPowerSeries (Fin 2) K) ∈ RingHom.ker (constantCoeff : MvPowerSeries (Fin 2) K →+* K) :=
    hle (htop ▸ Submodule.mem_top)
  rw [RingHom.mem_ker, map_one] at h1
  exact one_ne_zero h1

theorem subst_injective_of_finite {d : ℕ} (g : Fin d → MvPowerSeries (Fin d) K)
    (hg : ∀ i, constantCoeff (g i) = 0)
    (hfin : Module.Finite K (MvPowerSeries (Fin d) K ⧸ Ideal.span (Set.range g)))
    (hpos : 0 < Module.finrank K (MvPowerSeries (Fin d) K ⧸ Ideal.span (Set.range g))) :
    Function.Injective (subst g : MvPowerSeries (Fin d) K → MvPowerSeries (Fin d) K) := by
  classical
  have hs : HasSubst g := hasSubst_of_constantCoeff_zero hg
  obtain ⟨-, -, b, hb⟩ :=
    MvPowerSeries.finite_flat_exists_basis_substAlgHom_of_finite_quotient g hg hfin
  rw [← coe_substAlgHom hs]
  refine (injective_iff_map_eq_zero (substAlgHom hs)).2 fun y hy => ?_
  rw [coe_substAlgHom hs] at hy
  obtain ⟨c₀, -, huniq⟩ := hb 0
  let c₁ : Fin (Module.finrank K (MvPowerSeries (Fin d) K ⧸ Ideal.span (Set.range g))) →
      MvPowerSeries (Fin d) K := fun i => if (i : ℕ) = 0 then y else 0
  have h1 : c₁ = c₀ := huniq c₁ (by
    show (0 : MvPowerSeries (Fin d) K) = ∑ i, subst g (c₁ i) * b i
    rw [eq_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    show subst g (if (i : ℕ) = 0 then y else 0) * b i = 0
    split_ifs
    · rw [hy, zero_mul]
    · rw [← coe_substAlgHom hs, map_zero, zero_mul])
  have h2 : (fun _ => (0 : MvPowerSeries (Fin d) K)) = c₀ := huniq _ (by
    show (0 : MvPowerSeries (Fin d) K) = ∑ i, subst g 0 * b i
    rw [eq_comm]
    exact Finset.sum_eq_zero fun i _ => by rw [← coe_substAlgHom hs, map_zero, zero_mul])
  have h3 := congrFun (h1.trans h2.symm) ⟨0, hpos⟩
  have h4 : c₁ ⟨0, hpos⟩ = y := if_pos rfl
  rw [← h4]
  exact h3

theorem subst_injective (e : Λ Φ) (hfin : Module.Finite K (KerAlgebra (ser e))) :
    Function.Injective (subst (ser e) : MvPowerSeries (Fin 2) K → MvPowerSeries (Fin 2) K) := by
  haveI : Nontrivial (KerAlgebra (ser e)) := Ideal.Quotient.nontrivial_iff.mpr (span_ser_ne_top e)
  have hpos : 0 < Module.finrank K (KerAlgebra (ser e)) := Module.finrank_pos
  exact subst_injective_of_finite (ser e) (ser_constantCoeff e) hfin hpos

theorem ne_zero_of_finite (e : Λ Φ) (hfin : Module.Finite K (KerAlgebra (ser e))) : e ≠ 0 := by
  intro h0
  have hinj := subst_injective e hfin
  rw [h0] at hinj
  have hs : HasSubst (ser (0 : Λ Φ)) := hasSubst_of_constantCoeff_zero (ser_constantCoeff 0)
  have h1 : subst (ser (0 : Λ Φ)) (X (0 : Fin 2) : MvPowerSeries (Fin 2) K) =
      subst (ser (0 : Λ Φ)) (0 : MvPowerSeries (Fin 2) K) := by
    rw [subst_X hs, ← coe_substAlgHom hs, map_zero]
    rfl
  have h2 := hinj h1
  have h3 := congrArg (coeff (Finsupp.single (0 : Fin 2) 1)) h2
  rw [coeff_X, if_pos rfl, map_zero] at h3
  exact one_ne_zero h3

variable (E : Λ Φ →+* Matrix (Fin 2) (Fin 2) ℚ_[r]) (hinj : Function.Injective E) (m : ℕ)
  (hm : ∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r]))
  (hm' : ∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r]))

theorem rpow_ne_zero (n : ℕ) : (r : ℚ_[r]) ^ n ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.2 hr.out.ne_zero)

include hm hm' in

theorem exists_apply_eq_smul_adjugate (e : Λ Φ) :
    ∃ f : Λ Φ, E f = (r : ℚ_[r]) ^ (2 * m) • (E e).adjugate := by
  obtain ⟨A, hA⟩ := hm' e
  obtain ⟨f, hf⟩ := hm A.adjugate
  refine ⟨f, ?_⟩
  have hmap : A.adjugate.map ((↑) : ℤ_[r] → ℚ_[r]) = (A.map ((↑) : ℤ_[r] → ℚ_[r])).adjugate :=
    RingHom.map_adjugate (PadicInt.Coe.ringHom (p := r)) A
  rw [hf, hmap, ← hA, Matrix.adjugate_smul, Fintype.card_fin, smul_smul]
  congr 1
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, ← pow_add, two_mul]

include hinj hm hm' in

theorem det_ne_zero_of_finite (e : Λ Φ) (hfin : Module.Finite K (KerAlgebra (ser e))) :
    (E e).det ≠ 0 := by
  intro hdet
  obtain ⟨f, hf⟩ := exists_apply_eq_smul_adjugate E m hm hm' e

  have hfe : f * e = 0 := hinj (by
    rw [map_mul, hf, smul_mul_assoc, Matrix.adjugate_mul, hdet, zero_smul, smul_zero, map_zero])

  have hsub := subst_injective e hfin
  have hf0 : f = 0 := by
    refine eq_zero_of_ser f fun i => hsub ?_
    have := congrFun (ser_mul f e) i
    rw [hfe, ser_zero] at this
    rw [← this]
    have hs : HasSubst (ser e) := hasSubst_of_constantCoeff_zero (ser_constantCoeff e)
    rw [← coe_substAlgHom hs, map_zero]

  rw [hf0, map_zero, eq_comm, smul_eq_zero] at hf
  have hadj : (E e).adjugate = 0 := hf.resolve_left (rpow_ne_zero (2 * m))
  have hEe : E e = 0 := by
    have := Matrix.adjugate_adjugate (E e) (by rw [Fintype.card_fin]; decide)
    rw [hadj, Matrix.adjugate_zero, Fintype.card_fin, show (2 : ℕ) - 2 = 0 from rfl, pow_zero,
      one_smul] at this
    exact this.symm
  have he0 : e = 0 := hinj (by rw [hEe, map_zero])
  exact ne_zero_of_finite e hfin he0

end Invertible

section Main

variable {r : ℕ} [hr : Fact r.Prime]

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
  have hgr_coe : (gr : Matrix (Fin 2) (Fin 2) ℚ_[r]) = (r : ℚ_[r]) • (1 : Matrix (Fin 2) (Fin 2) ℚ_[r]) := rfl
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
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m'))) :
    ∃ u : ℤ_[r]ˣ, (E e).det = ((u : ℤ_[r]) : ℚ_[r]) * (r : ℚ_[r]) ^ m' := by

  letI : Field (WittVector r k ⧸ pIdeal r (WittVector r k)) := (isField_quot k).toField
  haveI : CharP (WittVector r k ⧸ pIdeal r (WittVector r k)) r := charP_quot k

  obtain ⟨hinj, m, hm, hm'⟩ := hE
  have hdet : (E e).det ≠ 0 := det_ne_zero_of_finite E hinj m hm hm' e he.1
  set g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet with hg
  have hg_coe : (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e := rfl

  obtain ⟨ν, hν4, hν⟩ :=
    CerednikDrinfeld.FormalODModule.exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
      (WittVector r k ⧸ pIdeal r (WittVector r k)) Φ hΦ4 E ⟨hinj, m, hm, hm'⟩
  obtain ⟨h, hνg, -, hfib⟩ := hν e g hg_coe

  have hh : h = 2 * m' := by
    have h1 := hfib (WittVector r k ⧸ pIdeal r (WittVector r k)) (RingHom.id _)
    have h2 := he.2.2 (WittVector r k ⧸ pIdeal r (WittVector r k)) (RingHom.id _)
    exact Nat.pow_right_injective hr.out.two_le (h1.symm.trans h2)

  obtain ⟨vdet, hvdet⟩ :=
    CerednikDrinfeld.exists_monoidHom_generalLinearGroup_eq_ofAdd_iff_of_irreducible ℤ_[r] inferInstance
      (r : ℤ_[r]) PadicInt.irreducible_p ℚ_[r] (Fin 2)
  obtain ⟨c, hc⟩ :=
    CerednikDrinfeld.exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic vdet hvdet ν
  have hνg' := nu_eq_two_mul vdet ν hvdet c hc hν4 g
  rw [hνg, hh] at hνg'
  have hv : Multiplicative.toAdd (vdet g) = m' := by
    have := Multiplicative.ofAdd.injective hνg'
    push_cast at this
    omega
  have hvm : vdet g = Multiplicative.ofAdd (m' : ℤ) := by
    rw [← hv]
    rfl
  obtain ⟨u, hu⟩ := (hvdet g m').1 hvm
  refine ⟨u, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, hg_coe, map_natCast, zpow_natCast] at hu
  exact hu

end Main

end R4DetHeight

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
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m'))) :
    ∃ u : ℤ_[r]ˣ, (E e).det = ((u : ℤ_[r]) : ℚ_[r]) * (r : ℚ_[r]) ^ m' :=
  R4DetHeight.main k ι Φ hΦ hΦ4 E hE e m' he

end S_CerednikDrinfeld_SpecialFormal_exists_det_eq_mul_pow_of_hasKernelOfDegree
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_exists_det_eq_mul_pow_of_hasKernelOfDegree (solution)
