-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.EquivariantUniformization.coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d5d216d4-a722-5d59-a537-9b1056f6fa39

import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    {E V : Type} [Fintype E] [DecidableEq V]
    {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {S : Type} [Group S]
    {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal)
    (σ : S) (hσ : actZ σ = 1)
    (s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion)
    (hs : ∀ c, s c = (scalar σ) • c)
    (hiso : ∀ c, Valued.v (s c) = Valued.v c)
    (u : 𝒰.P.TorusPoints) (hu : gal σ (𝒰.eFull u) = 𝒰.eFull u) :
    𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u = u := by
  classical
  letI instField : Field A.valuation.Completion := inferInstance
  letI instCR : CommRing A.valuation.Completion := inferInstance
  set sR : A.valuation.Completion →+* A.valuation.Completion :=
    (s : A.valuation.Completion →+* A.valuation.Completion) with hsR

  have hpos : ∀ y : ↥(ribbonKernel D), ribbonGram D y y = 0 → y = 0 := by
    intro y hy
    rw [ribbonGram_apply] at hy
    have hterm : ∀ e ∈ (Finset.univ : Finset E), (0 : ℤ) ≤ (D.w e : ℤ) * (y.1 e * y.1 e) :=
      fun e _ => mul_nonneg (by exact_mod_cast (D.w e).pos.le) (mul_self_nonneg _)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hy
    refine Subtype.ext (funext fun e => ?_)
    have he := hzero e (Finset.mem_univ e)
    have hw : (D.w e : ℤ) ≠ 0 := by exact_mod_cast (D.w e).pos.ne'
    have := (mul_eq_zero.mp he).resolve_left hw
    simpa using mul_self_eq_zero.mp this

  have hpre : 𝒰.P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) :
      ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) u = u := by
    refine LinearMap.ext fun z => ?_
    rw [PeriodDatum.precomp_apply, hσ, inv_one]
    rfl

  have h2 : 𝒰.eFull (𝒰.P.coeffMap sR u) =
      𝒰.eFull u := by
    have h := 𝒰.eFull_equiv σ s hs u
    rw [hpre] at h
    rw [h, hu]

  have h3 : 𝒰.P.coeffMap sR u - u ∈
      𝒰.P.periodLattice := by
    rw [← 𝒰.eFull_ker, map_sub, h2, sub_self]
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp h3

  have h4 := LinearMap.congr_fun hy y
  rw [PeriodDatum.QL_apply, LinearMap.sub_apply, PeriodDatum.coeffMap_apply] at h4
  have h5 : Units.map (algebraMap (↥𝒰.K) A.valuation.Completion).toMonoidHom
      (Additive.toMul (𝒰.P.Q y y)) =
      Units.map (sR :
        A.valuation.Completion →* A.valuation.Completion) (Additive.toMul (u y)) /
        Additive.toMul (u y) := by
    have := congrArg Additive.toMul h4
    rwa [← ofMul_toMul (𝒰.P.Q y y), unitsBaseChange_apply, toMul_ofMul, toMul_sub,
      toMul_ofMul] at this
  have h6 : Valued.v ((((Additive.toMul (𝒰.P.Q y y) : (↥𝒰.K)ˣ) : ↥𝒰.K) :
        A.valuation.Completion)) =
      Valued.v (s ((Additive.toMul (u y) : (A.valuation.Completion)ˣ) : A.valuation.Completion)) /
        Valued.v ((Additive.toMul (u y) : (A.valuation.Completion)ˣ) : A.valuation.Completion) := by
    have := congrArg (fun x : (A.valuation.Completion)ˣ => Valued.v (x : A.valuation.Completion)) h5
    simp [Units.val_div_eq_div_val, map_div₀] at this
    exact this
  rw [hiso, div_self ((Valuation.ne_zero_iff _).mpr (Units.ne_zero _))] at h6

  have h7 : Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ribbonGram D y y) = 1 := by
    rw [← 𝒰.P.ord_Q y y, ← h6]
    have := 𝒰.ord_spec (Additive.toMul (𝒰.P.Q y y))
    rw [ofMul_toMul] at this
    exact this.symm

  have hr1 : Valued.v ((r : ℕ) : A.valuation.Completion) < 1 := by
    have hc : ((r : ℕ) : A.valuation.Completion) =
        ((WithVal.toVal A.valuation ((r : ℕ) : AlgebraicClosure ℚ) : WithVal A.valuation) :
          A.valuation.Completion) := by
      rw [WithVal.toVal_natCast,
        ← map_natCast (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)) r]
      rfl
    rw [hc, Valued.valuedCompletion_apply, WithVal.valued_toVal]
    exact (A.mem_nonunits_iff).mp hA
  have hr0 : Valued.v ((r : ℕ) : A.valuation.Completion) ≠ 0 := by
    rw [Valuation.ne_zero_iff, Nat.cast_ne_zero]
    exact (Fact.out : r.Prime).ne_zero

  have hnn : 0 ≤ ribbonGram D y y := by
    rw [ribbonGram_apply]
    exact Finset.sum_nonneg fun e _ =>
      mul_nonneg (by exact_mod_cast (D.w e).pos.le) (mul_self_nonneg _)
  have hG : ribbonGram D y y = 0 := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
    rw [hn] at h7 ⊢
    rw [zpow_natCast] at h7
    by_contra hne
    exact (pow_lt_one₀ zero_le' hr1 (by exact_mod_cast hne)).ne h7
  have hy0 : y = 0 := hpos y hG

  have hfin : 𝒰.P.coeffMap sR u - u = 0 := by
    rw [← hy, hy0, LinearMap.map_zero]
  exact sub_eq_zero.mp hfin

end S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_coeffMap_eq_of_actZ_eq_one_of_gal_eFull_eq (solution)
