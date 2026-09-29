-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.PeriodDatum.exists_torsionEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e04a29a5-4dfc-5ab5-a759-ea36334cc074

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_exists_torsionEquiv

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) {p : ℕ} [Fact p.Prime] {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p) :
    ∃ e : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ)) ≃ₗ[ℤ] (↥(ribbonKernel D) →ₗ[ℤ] ZMod p),
      ∀ (v : ↥(Submodule.torsionBy ℤ ↥P.U (p : ℤ))) (z : ↥(ribbonKernel D)),
        ((v : ↥P.U) : P.TorusPoints) z = Additive.ofMul (ζ ^ (e v z).val) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩

  have hmod : ∀ m : ℕ, ζ ^ (m % p) = ζ ^ m := by
    intro m
    conv_rhs => rw [← Nat.mod_add_div m p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  let χ : ZMod p →+ Additive Lˣ :=
    { toFun := fun a => Additive.ofMul (ζ ^ a.val)
      map_zero' := by simp only [ZMod.val_zero, pow_zero, ofMul_one]
      map_add' := by
        intro a b
        rw [ZMod.val_add, hmod, pow_add, ofMul_mul] }
  have hχ : ∀ a : ZMod p, χ a = Additive.ofMul (ζ ^ a.val) := fun a => rfl
  have hχp : ∀ a : ZMod p, p • χ a = 0 := by
    intro a
    rw [hχ, ← ofMul_pow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, ofMul_one]
  have hχinj : Function.Injective χ := by
    intro a b hab
    rw [hχ, hχ] at hab
    have h' : ζ ^ a.val = ζ ^ b.val := Additive.ofMul.injective hab
    exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h')

  set T := Submodule.torsionBy ℤ ↥P.U (p : ℤ) with hT
  have hval : ∀ (v : ↥T) (z : ↥(ribbonKernel D)),
      (Additive.toMul (((v : ↥P.U) : P.TorusPoints) z)) ^ p = 1 := by
    intro v z
    have hv : (p : ℤ) • (v : ↥P.U) = 0 := (Submodule.mem_torsionBy_iff (p : ℤ) (v : ↥P.U)).mp v.2
    have h1 : (p : ℤ) • ((v : ↥P.U) : P.TorusPoints) = 0 := by
      rw [← Submodule.coe_smul, hv, Submodule.coe_zero]
    have hv' := LinearMap.congr_fun h1 z
    rw [LinearMap.smul_apply, LinearMap.zero_apply, natCast_zsmul] at hv'
    have := congrArg Additive.toMul hv'
    rwa [toMul_nsmul, toMul_zero] at this

  have hlog : ∀ (v : ↥T) (z : ↥(ribbonKernel D)), ∃ i : ℕ, i < p ∧
      ζ ^ i = Additive.toMul (((v : ↥P.U) : P.TorusPoints) z) := by
    intro v z
    obtain ⟨i, hi, h⟩ := hζ.eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity p _).mpr (hval v z))
    exact ⟨i, hi, h⟩
  choose lg hlg_lt hlg using hlog

  have hf : ∀ (v : ↥T) (z : ↥(ribbonKernel D)),
      χ ((lg v z : ℕ) : ZMod p) = ((v : ↥P.U) : P.TorusPoints) z := by
    intro v z
    rw [hχ, ZMod.val_cast_of_lt (hlg_lt v z), hlg, ofMul_toMul]

  let fv : ∀ v : ↥T, ↥(ribbonKernel D) →ₗ[ℤ] ZMod p := fun v =>
    (AddMonoidHom.mk' (fun z => ((lg v z : ℕ) : ZMod p)) (by
      intro z z'
      apply hχinj
      rw [map_add, hf, hf, hf, map_add])).toIntLinearMap
  have hfv : ∀ (v : ↥T) (z : ↥(ribbonKernel D)), fv v z = ((lg v z : ℕ) : ZMod p) := fun v z => rfl
  have hfvχ : ∀ (v : ↥T) (z : ↥(ribbonKernel D)), χ (fv v z) = ((v : ↥P.U) : P.TorusPoints) z := by
    intro v z; rw [hfv, hf]

  let e₀ : ↥T →ₗ[ℤ] (↥(ribbonKernel D) →ₗ[ℤ] ZMod p) :=
    (AddMonoidHom.mk' fv (by
      intro v v'
      refine LinearMap.ext fun z => ?_
      apply hχinj
      rw [LinearMap.add_apply, map_add, hfvχ, hfvχ, hfvχ]
      rfl)).toIntLinearMap
  have he₀ : ∀ v : ↥T, e₀ v = fv v := fun v => rfl

  have hinj : Function.Injective e₀ := by
    intro v v' h
    apply Subtype.ext; apply Subtype.ext
    refine LinearMap.ext fun z => ?_
    rw [← hfvχ v z, ← hfvχ v' z, ← he₀, ← he₀, h]
  have hsurj : Function.Surjective e₀ := by
    intro f
    let w : P.TorusPoints := χ.toIntLinearMap ∘ₗ f
    have hw : ∀ z, w z = χ (f z) := fun z => rfl
    have hpw : (p : ℤ) • w = 0 := by
      refine LinearMap.ext fun z => ?_
      rw [LinearMap.smul_apply, hw, natCast_zsmul, hχp, LinearMap.zero_apply]
    have hwU : w ∈ P.U := by
      simp only [PeriodDatum.U, Submodule.mem_comap]
      refine (Submodule.mem_torsion_iff _).mpr
        ⟨⟨(p : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp.ne_zero)⟩, ?_⟩
      show (p : ℤ) • P.periodLattice.mkQ w = 0
      rw [← map_zsmul, hpw, map_zero]
    have hwT : (⟨w, hwU⟩ : ↥P.U) ∈ T := by
      rw [hT, Submodule.mem_torsionBy_iff]
      apply Subtype.ext
      exact hpw
    refine ⟨⟨⟨w, hwU⟩, hwT⟩, ?_⟩
    refine LinearMap.ext fun z => ?_
    apply hχinj
    rw [he₀, hfvχ]
    exact hw z
  refine ⟨LinearEquiv.ofBijective e₀ ⟨hinj, hsurj⟩, fun v z => ?_⟩
  rw [LinearEquiv.ofBijective_apply, he₀, ← hχ, hfvχ]

end S_CerednikDrinfeld_Mumford_PeriodDatum_exists_torsionEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_exists_torsionEquiv (solution)
