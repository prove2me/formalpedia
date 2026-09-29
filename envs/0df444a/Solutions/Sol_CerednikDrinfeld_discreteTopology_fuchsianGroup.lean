-- Prove2me | solution 1 for CerednikDrinfeld.discreteTopology_fuchsianGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b1d3de4f-6b48-5398-862b-3da2160100ee

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_discreteTopology_fuchsianGroup

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

namespace DiscFuchsian

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

universe u

theorem eq_zero_of_smul_one_add_smul_eq_zero {A : Type u} [Ring A] [Algebra ℝ A] [Nontrivial A]
    {I J : A} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hI : I * I = a • (1 : A)) (hJ : J * J = b • (1 : A)) (hIJ : I * J = -(J * I))
    {x y : ℝ} (h : x • (1 : A) + y • I = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · subst hy
    simp only [zero_smul, add_zero] at h
    exact ⟨(smul_eq_zero.mp h).resolve_right one_ne_zero, rfl⟩
  · exfalso
    have h' : y • I = -(x • (1 : A)) := by linear_combination (norm := module) h
    have hIc : I = (-(x / y)) • (1 : A) := by
      calc I = y⁻¹ • (y • I) := by rw [smul_smul, inv_mul_cancel₀ hy, one_smul]
        _ = (-(x / y)) • (1 : A) := by rw [h', div_eq_mul_inv]; module
    have h1 : I * J = (-(x / y)) • J := by rw [hIc, smul_mul_assoc, one_mul]
    have h2 : J * I = (-(x / y)) • J := by rw [hIc, mul_smul_comm, mul_one]
    rw [h1, h2] at hIJ
    have hc : (-(x / y)) • J = 0 := by linear_combination (norm := module) (2⁻¹ : ℝ) • hIJ
    rcases smul_eq_zero.mp hc with hc0 | hJ0
    · have hI0 : I = 0 := by rw [hIc, hc0, zero_smul]
      have : a • (1 : A) = 0 := by rw [← hI, hI0, mul_zero]
      exact ha ((smul_eq_zero.mp this).resolve_right one_ne_zero)
    · have : b • (1 : A) = 0 := by rw [← hJ, hJ0, mul_zero]
      exact hb ((smul_eq_zero.mp this).resolve_right one_ne_zero)

theorem linearIndependent_one_I_J_IJ {A : Type u} [Ring A] [Algebra ℝ A] [Nontrivial A]
    {I J : A} {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hI : I * I = a • (1 : A)) (hJ : J * J = b • (1 : A)) (hIJ : I * J = -(J * I)) :
    LinearIndependent ℝ ![(1 : A), I, J, I * J] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hZ : g 0 • (1 : A) + g 1 • I + g 2 • J + g 3 • (I * J) = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have hJI : J * I = -(I * J) := by rw [hIJ, neg_neg]
  have hIIJ : I * (I * J) = a • J := by rw [← mul_assoc, hI, smul_mul_assoc, one_mul]
  have hIJI : I * J * I = -(a • J) := by rw [mul_assoc, hJI, mul_neg, hIIJ]
  have hIJJ : I * J * J = b • I := by rw [mul_assoc, hJ, mul_smul_comm, mul_one]

  have e1 : I * (g 0 • (1 : A) + g 1 • I + g 2 • J + g 3 • (I * J)) +
      (g 0 • (1 : A) + g 1 • I + g 2 • J + g 3 • (I * J)) * I =
      (2 * a * g 1) • (1 : A) + (2 * g 0) • I := by
    simp only [mul_add, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    rw [hI, hIIJ, hJI, hIJI]
    module
  have h1 : (2 * a * g 1) • (1 : A) + (2 * g 0) • I = 0 := by
    rw [← e1, hZ, mul_zero, zero_mul, add_zero]
  obtain ⟨h1a, h1b⟩ := eq_zero_of_smul_one_add_smul_eq_zero ha hb hI hJ hIJ h1
  have hg1 : g 1 = 0 := by
    rcases mul_eq_zero.mp h1a with h | h
    · exact absurd (mul_eq_zero.mp h) (by simp [ha])
    · exact h
  have hg0 : g 0 = 0 := by simpa using h1b

  have hZ2 : g 2 • J + g 3 • (I * J) = 0 := by
    simpa [hg0, hg1] using hZ
  have e2 : (g 2 • J + g 3 • (I * J)) * J = (b * g 2) • (1 : A) + (b * g 3) • I := by
    simp only [add_mul, smul_mul_assoc]
    rw [hJ, hIJJ]
    module
  have h2 : (b * g 2) • (1 : A) + (b * g 3) • I = 0 := by rw [← e2, hZ2, zero_mul]
  obtain ⟨h2a, h2b⟩ := eq_zero_of_smul_one_add_smul_eq_zero ha hb hI hJ hIJ h2
  have hg2 : g 2 = 0 := by simpa [hb] using h2a
  have hg3 : g 3 = 0 := by simpa [hb] using h2b
  intro i
  fin_cases i <;> assumption

end DiscFuchsian

open DiscFuchsian in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem solution {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    DiscreteTopology ↥(fuchsianGroup R ι) := by
  classical

  let qi : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩
  let qj : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩
  have hqi : qi * qi = a • (1 : ℍ[ℚ, a, b]) := by ext <;> simp [qi]
  have hqj : qj * qj = b • (1 : ℍ[ℚ, a, b]) := by ext <;> simp [qj]
  have hqij : qi * qj = -(qj * qi) := by ext <;> simp [qi, qj]
  have hqk : qi * qj = (⟨0, 0, 0, 1⟩ : ℍ[ℚ, a, b]) := by ext <;> simp [qi, qj]
  have hdec : ∀ u : ℍ[ℚ, a, b],
      u = u.re • (1 : ℍ[ℚ, a, b]) + u.imI • qi + u.imJ • qj + u.imK • (qi * qj) := by
    intro u; rw [hqk]; ext <;> simp [qi, qj]
  set a' : ℝ := algebraMap ℚ ℝ a with ha'd
  set b' : ℝ := algebraMap ℚ ℝ b with hb'd
  have ha' : a' ≠ 0 := by rw [ha'd]; exact (map_ne_zero _).mpr ha
  have hb' : b' ≠ 0 := by rw [hb'd]; exact (map_ne_zero _).mpr hb
  set I : Matrix (Fin 2) (Fin 2) ℝ := ι qi with hIdef
  set J : Matrix (Fin 2) (Fin 2) ℝ := ι qj with hJdef
  have hI : I * I = a' • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hIdef, ← map_mul, hqi, map_smul, map_one, ha'd, algebraMap_smul]
  have hJ : J * J = b' • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hJdef, ← map_mul, hqj, map_smul, map_one, hb'd, algebraMap_smul]
  have hIJ : I * J = -(J * I) := by
    rw [hIdef, hJdef, ← map_mul, ← map_mul, hqij, map_neg]
  have hind := linearIndependent_one_I_J_IJ ha' hb' hI hJ hIJ
  have hcard : Fintype.card (Fin 4) = Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℝ) := by
    simp [Module.finrank_matrix]
  let B : Module.Basis (Fin 4) ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
    basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hB : ∀ n, B n = ![(1 : Matrix (Fin 2) (Fin 2) ℝ), I, J, I * J] n := fun n =>
    coe_basisOfLinearIndependentOfCardEqFinrank hind hcard ▸ rfl

  obtain ⟨S, hS⟩ := hR.fg
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
    (S.biUnion fun u => ({u.re, u.imI, u.imJ, u.imK} : Finset ℚ))
  have hd0 : ((d : ℤ) : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.coe_ne_zero d

  have hcoord : ∀ φ : ℍ[ℚ, a, b] →+ ℚ,
      (∀ s ∈ S, φ s ∈ ({s.re, s.imI, s.imJ, s.imK} : Finset ℚ)) →
      ∀ u ∈ R, ∃ z : ℤ, (z : ℚ) = (d : ℤ) * φ u := by
    intro φ hφ u hu
    rw [← hS] at hu
    induction hu using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨z, hz⟩ := hd (φ s) (Finset.mem_biUnion.mpr ⟨s, hs, hφ s hs⟩)
      exact ⟨z, by simpa [zsmul_eq_mul] using hz⟩
    | zero => exact ⟨0, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨z, hz⟩ := hu; obtain ⟨w, hw⟩ := hv
      exact ⟨z + w, by push_cast; rw [hz, hw, map_add]; ring⟩
    | smul m u _ hu =>
      obtain ⟨z, hz⟩ := hu
      exact ⟨m * z, by push_cast; rw [hz, map_zsmul, zsmul_eq_mul]; push_cast; ring⟩
  let φre : ℍ[ℚ, a, b] →+ ℚ := AddMonoidHom.mk' (fun u => u.re) (fun _ _ => rfl)
  let φI : ℍ[ℚ, a, b] →+ ℚ := AddMonoidHom.mk' (fun u => u.imI) (fun _ _ => rfl)
  let φJ : ℍ[ℚ, a, b] →+ ℚ := AddMonoidHom.mk' (fun u => u.imJ) (fun _ _ => rfl)
  let φK : ℍ[ℚ, a, b] →+ ℚ := AddMonoidHom.mk' (fun u => u.imK) (fun _ _ => rfl)

  let B' : Module.Basis (Fin 4) ℝ (Matrix (Fin 2) (Fin 2) ℝ) :=
    B.unitsSMul fun _ => Units.mk0 (((d : ℤ) : ℝ))⁻¹ (inv_ne_zero hd0)
  have hB' : ∀ n, B' n = (((d : ℤ) : ℝ))⁻¹ • ![(1 : Matrix (Fin 2) (Fin 2) ℝ), I, J, I * J] n := by
    intro n; rw [Module.Basis.unitsSMul_apply, hB n, Units.smul_mk0]
  have hB0 : B' 0 = (((d : ℤ) : ℝ))⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by rw [hB']; rfl
  have hB1 : B' 1 = (((d : ℤ) : ℝ))⁻¹ • I := by rw [hB']; rfl
  have hB2 : B' 2 = (((d : ℤ) : ℝ))⁻¹ • J := by rw [hB']; rfl
  have hB3 : B' 3 = (((d : ℤ) : ℝ))⁻¹ • (I * J) := by rw [hB']; rfl
  have key : ∀ (q : ℚ) (z : ℤ) (X : Matrix (Fin 2) (Fin 2) ℝ), (z : ℚ) = (d : ℤ) * q →
      q • X = z • ((((d : ℤ) : ℝ))⁻¹ • X) := by
    intro q z X hqz
    have hq : (q : ℝ) = (z : ℝ) * (((d : ℤ) : ℝ))⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hd0, mul_comm]; exact_mod_cast hqz.symm
    rw [← Rat.cast_smul_eq_qsmul ℝ q X, hq, mul_smul, Int.cast_smul_eq_zsmul]
  have hmemL : ∀ u ∈ R, ι u ∈ Submodule.span ℤ (Set.range ⇑B') := by
    intro u hu
    obtain ⟨z0, hz0⟩ := hcoord φre (fun s _ => by simp [φre]) u hu
    obtain ⟨z1, hz1⟩ := hcoord φI (fun s _ => by simp [φI]) u hu
    obtain ⟨z2, hz2⟩ := hcoord φJ (fun s _ => by simp [φJ]) u hu
    obtain ⟨z3, hz3⟩ := hcoord φK (fun s _ => by simp [φK]) u hu
    have hιu : ι u = z0 • B' 0 + z1 • B' 1 + z2 • B' 2 + z3 • B' 3 := by
      conv_lhs => rw [hdec u]
      rw [map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, map_one, map_mul,
        ← hIdef, ← hJdef, hB0, hB1, hB2, hB3,
        key u.re z0 _ hz0, key u.imI z1 _ hz1, key u.imJ z2 _ hz2, key u.imK z3 _ hz3]
    rw [hιu]
    refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

  have hunit : ∀ v ∈ unitGroup R, (v : ℍ[ℚ, a, b]) ∈ R := by
    let U : Subgroup (ℍ[ℚ, a, b])ˣ :=
      { carrier := {v | (v : ℍ[ℚ, a, b]) ∈ R ∧ ((v⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R}
        one_mem' := ⟨by simpa using hR.one_mem, by simpa using hR.one_mem⟩
        mul_mem' := by
          rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
          refine ⟨by push_cast; exact hR.mul_mem hx hy, ?_⟩
          rw [mul_inv_rev]; push_cast; exact hR.mul_mem hy' hx'
        inv_mem' := by
          rintro x ⟨hx, hx'⟩
          exact ⟨hx', by simpa using hx⟩ }
    have hle : unitGroup R ≤ U := by
      rw [unitGroup, Subgroup.closure_le]
      rintro v ⟨hv, w, hw, hvw, -⟩
      exact ⟨hv, by rwa [Units.inv_eq_of_mul_eq_one_right hvw]⟩
    intro v hv
    exact (hle hv).1

  have hval : ∀ γ : ↥(fuchsianGroup R ι),
      ((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) ∈ Submodule.span ℤ (Set.range ⇑B') := by
    rintro ⟨γ, hγ⟩
    obtain ⟨hγmap, -⟩ := Subgroup.mem_inf.mp hγ
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hγmap
    simpa using hmemL v (hunit v hv)
  let f : ↥(fuchsianGroup R ι) → ↥(Submodule.span ℤ (Set.range ⇑B')) :=
    fun γ => ⟨((γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ), hval γ⟩
  have hfc : Continuous f :=
    (Units.continuous_val.comp continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    rintro ⟨γ, _⟩ ⟨γ', _⟩ h
    exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  have hL : DiscreteTopology ↥(Submodule.span ℤ (Set.range ⇑B')) :=
    ZSpan.instDiscreteTopologySubtypeMemSubmoduleIntSpanRangeCoeBasisRealOfFinite B'
  exact @DiscreteTopology.of_continuous_injective _ _ _ _ hL _ hfc hfi

end S_CerednikDrinfeld_discreteTopology_fuchsianGroup
end P2MW
export P2MW.S_CerednikDrinfeld_discreteTopology_fuchsianGroup (solution)
