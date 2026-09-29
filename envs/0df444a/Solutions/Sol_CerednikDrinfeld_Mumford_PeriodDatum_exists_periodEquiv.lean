-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.PeriodDatum.exists_periodEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d945a2f0-97bf-5907-ad66-477fc3b5701f

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_exists_periodEquiv

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) :
    ∃ e : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(LinearMap.ker P.π),
      ∀ x : ↥(ribbonKernel D), ((e x : ↥P.U) : P.TorusPoints) = P.QL x := by

  have hinj : Function.Injective (unitsBaseChange K L) := by
    intro u v huv
    have huv' : Units.map (algebraMap K L).toMonoidHom (Additive.toMul u)
        = Units.map (algebraMap K L).toMonoidHom (Additive.toMul v) := huv
    have hval := congrArg (fun w : Lˣ => (w : L)) huv'
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hval
    exact Additive.toMul.injective (Units.ext ((algebraMap K L).injective hval))

  have pos : ∀ z : ↥(ribbonKernel D), z ≠ 0 → 0 < ribbonGram D z z := by
    intro z hz
    have hz1 : (z : E → ℤ) ≠ 0 := fun h => hz (Subtype.ext h)
    obtain ⟨e₀, he₀⟩ := Function.ne_iff.mp hz1
    rw [ribbonGram_apply]
    refine Finset.sum_pos' (fun e _ => ?_) ⟨e₀, Finset.mem_univ _, ?_⟩
    · exact mul_nonneg (by positivity) (mul_self_nonneg _)
    · exact mul_pos (by exact_mod_cast (D.w e₀).pos) (mul_self_pos.mpr he₀)
  have hQinj : Function.Injective P.Q := by
    intro x x' hxx'
    by_contra hne
    have hz : x - x' ≠ 0 := sub_ne_zero.mpr hne
    have hQ : P.Q (x - x') (x - x') = 0 := by
      rw [LinearMap.map_sub₂, hxx', sub_self]
    have h0 : ribbonGram D (x - x') (x - x') = 0 := by
      rw [← P.ord_Q, hQ, map_zero]
    exact (pos (x - x') hz).ne' h0
  have hQLinj : Function.Injective P.QL := by
    intro x x' h
    apply hQinj
    refine LinearMap.ext fun y => ?_
    have hy := LinearMap.congr_fun h y
    simp only [PeriodDatum.QL_apply] at hy
    exact hinj hy

  have hlat : ∀ x, P.periodLattice.mkQ (P.QL x) = 0 := fun x =>
    (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ x)
  have hmemU : ∀ x, P.QL x ∈ P.U := by
    intro x
    simp only [PeriodDatum.U, Submodule.mem_comap]
    rw [hlat x]
    exact Submodule.zero_mem _
  let f : ↥(ribbonKernel D) →ₗ[ℤ] ↥P.U := LinearMap.codRestrict P.U P.QL hmemU
  have hker : ∀ x, f x ∈ LinearMap.ker P.π := by
    intro x
    rw [LinearMap.mem_ker]
    exact hlat x
  let g : ↥(ribbonKernel D) →ₗ[ℤ] ↥(LinearMap.ker P.π) := LinearMap.codRestrict (LinearMap.ker P.π) f hker
  have hg : ∀ x, ((g x : ↥P.U) : P.TorusPoints) = P.QL x := fun x => rfl
  refine ⟨LinearEquiv.ofBijective g ⟨?_, ?_⟩, fun x => ?_⟩
  · intro x x' h
    apply hQLinj
    rw [← hg x, ← hg x', h]
  · rintro ⟨u, hu⟩
    rw [LinearMap.mem_ker] at hu
    have hu' : (u : P.TorusPoints) ∈ P.periodLattice := (Submodule.Quotient.mk_eq_zero _).mp hu
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hu'
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rw [hg x]
    exact hx
  · rw [LinearEquiv.ofBijective_apply]
    exact hg x

end S_CerednikDrinfeld_Mumford_PeriodDatum_exists_periodEquiv
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_exists_periodEquiv (solution)
