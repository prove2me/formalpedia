-- Prove2me | solution 1 for CerednikDrinfeld.Mumford.EquivariantUniformization.eFull_restrict_U_torsion_and_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/663de59c-7f4b-57d0-a5bc-93acfaa8e42f

import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_eFull_restrict_U_torsion_and_equiv

set_option autoImplicit false

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_eFull_restrict_U_torsion_and_equiv.CerednikDrinfeld CerednikDrinfeld.Mumford P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_eFull_restrict_U_torsion_and_equiv.CerednikDrinfeld.Mumford ModularCurve"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Mumford.EquivariantUniformization DegeneracyData ribbonKernel"
namespace Mumford
p2m_export "CerednikDrinfeld.Mumford" "EquivariantUniformization PeriodDatum.precomp_apply PeriodDatum PeriodDatum.U"
namespace EquivariantUniformization
p2m_export "CerednikDrinfeld.Mumford.EquivariantUniformization" "eFull_surjective eFull_ker P eFull eFull_equiv Q_equiv K"
p2m_open "CerednikDrinfeld.Mumford.EquivariantUniformization CerednikDrinfeld.Mumford CerednikDrinfeld"

private theorem _root_.CerednikDrinfeld.Mumford.EquivariantUniformization.mem_U_iff'
    {E V : Type} [Fintype E] [DecidableEq V] {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {S : Type} [Group S] {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal) (u : 𝒰.P.TorusPoints) :
    u ∈ 𝒰.P.U ↔ ∃ n : ℤ, n ≠ 0 ∧ n • u ∈ 𝒰.P.periodLattice := by
  rw [PeriodDatum.U, Submodule.mem_comap]
  constructor
  · intro hu
    have h := (Submodule.mem_torsion_iff _).mp hu
    refine ⟨(h.choose : ℤ), nonZeroDivisors.coe_ne_zero h.choose, ?_⟩
    have h2 : (h.choose : ℤ) • 𝒰.P.periodLattice.mkQ u = 0 := h.choose_spec
    rwa [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  · intro h
    refine (Submodule.mem_torsion_iff _).mpr ⟨⟨h.choose, mem_nonZeroDivisors_of_ne_zero h.choose_spec.1⟩, ?_⟩
    rw [Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h.choose_spec.2

p2m_export "CerednikDrinfeld.Mumford.EquivariantUniformization" "mem_U_iff'"
end CerednikDrinfeld.Mumford.EquivariantUniformization

theorem solution
    {E V : Type} [Fintype E] [DecidableEq V] {r : ℕ} [Fact r.Prime] {D : DegeneracyData E V}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime r}
    {T : Type} [AddCommGroup T] {S : Type} [Group S] {scalar : S →* ↥(A.decompositionSubgroup ℚ)}
    {actZ : S →* (↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D))} {gal : S →* AddAut T}
    (𝒰 : EquivariantUniformization r D A hA T S scalar actZ gal) :
    (∀ t : T, IsOfFinAddOrder t → t ∈ (𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom).range) ∧
    (∀ u : ↥𝒰.P.U, IsOfFinAddOrder ((𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom) u)) ∧
    (∀ u : ↥𝒰.P.U, (𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom) u = 0 ↔ (u : 𝒰.P.TorusPoints) ∈ 𝒰.P.periodLattice) ∧
    (∀ σ : S, actZ σ = 1 → ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = (scalar σ) • c) →
      ∀ (u : ↥𝒰.P.U) (hu : 𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : 𝒰.P.TorusPoints) ∈ 𝒰.P.U),
        (𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom) ⟨𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) (u : 𝒰.P.TorusPoints), hu⟩ =
          gal σ ((𝒰.eFull.comp 𝒰.P.U.subtype.toAddMonoidHom) u)) ∧
    (∀ σ : S, actZ σ = 1 → ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = (scalar σ) • c) →
      ∀ u : 𝒰.P.TorusPoints,
        𝒰.eFull (𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u) = gal σ (𝒰.eFull u)) ∧
    (∀ σ : S, actZ σ = 1 → ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = (scalar σ) • c) →
      ∀ x y : ↥(ribbonKernel D),
        s (((Additive.toMul (𝒰.P.Q x y) : (↥𝒰.K)ˣ) : ↥𝒰.K) : A.valuation.Completion) =
          (((Additive.toMul (𝒰.P.Q x y) : (↥𝒰.K)ˣ) : ↥𝒰.K) : A.valuation.Completion)) := by

  have h4 : ∀ σ : S, actZ σ = 1 → ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = (scalar σ) • c) →
      ∀ u : 𝒰.P.TorusPoints, 𝒰.eFull (𝒰.P.coeffMap (s : A.valuation.Completion →+* A.valuation.Completion) u) = gal σ (𝒰.eFull u) := by
    intro σ hσ s hs u
    have h := 𝒰.eFull_equiv σ s hs u
    have hpre : 𝒰.P.precomp (((actZ σ)⁻¹ : ↥(ribbonKernel D) ≃ₗ[ℤ] ↥(ribbonKernel D)) :
        ↥(ribbonKernel D) →ₗ[ℤ] ↥(ribbonKernel D)) u = u := by
      apply LinearMap.ext
      intro z
      rw [PeriodDatum.precomp_apply, hσ, inv_one]
      rfl
    rw [hpre] at h
    exact h
  refine ⟨fun t ht => ?_, fun u => ?_, fun u => 𝒰.eFull_ker u, fun σ hσ s hs u hu => h4 σ hσ s hs u, h4,
    fun σ hσ s hs x y => ?_⟩
  ·
    have hv := 𝒰.eFull_surjective t
    have hn := (isOfFinAddOrder_iff_nsmul_eq_zero.mp ht)
    let v : 𝒰.P.TorusPoints := hv.choose
    have hvt : 𝒰.eFull v = t := hv.choose_spec
    let n : ℕ := hn.choose
    have hn0 : 0 < n := hn.choose_spec.1
    have hnt : n • t = 0 := hn.choose_spec.2
    have hmem : v ∈ 𝒰.P.U := by
      rw [CerednikDrinfeld.Mumford.EquivariantUniformization.mem_U_iff']
      refine ⟨(n : ℤ), by exact_mod_cast hn0.ne', ?_⟩
      rw [← 𝒰.eFull_ker, natCast_zsmul, map_nsmul, hvt, hnt]
    exact ⟨⟨v, hmem⟩, hvt⟩
  ·
    have h := (𝒰.mem_U_iff' (u : 𝒰.P.TorusPoints)).mp u.2
    rw [isOfFinAddOrder_iff_zsmul_eq_zero]
    refine ⟨h.choose, h.choose_spec.1, ?_⟩
    rw [← map_zsmul]
    show 𝒰.eFull ((h.choose • u : ↥𝒰.P.U) : 𝒰.P.TorusPoints) = 0
    rw [Submodule.coe_smul, 𝒰.eFull_ker]
    exact h.choose_spec.2
  ·
    have h := 𝒰.Q_equiv σ s hs x y
    rw [hσ] at h
    exact h

end S_CerednikDrinfeld_Mumford_EquivariantUniformization_eFull_restrict_U_torsion_and_equiv
end P2MW
export P2MW.S_CerednikDrinfeld_Mumford_EquivariantUniformization_eFull_restrict_U_torsion_and_equiv (solution)
