-- Prove2me | solution 1 for CerednikDrinfeld.exists_isCompact_finset_forall_sl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/544b500e-7590-5769-9259-a3a52d47851f

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_basis_span_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_exists_intCast_eq_nrd_and_exists_intCast_eq_trd
import Theorems.Thm_CerednikDrinfeld_det_map_eq_nrd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_isCompact_finset_forall_sl

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open MeasureTheory

namespace MinkAux

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

end MinkAux

namespace MinkAux

theorem det_mulRight (g : Matrix (Fin 2) (Fin 2) ℝ) :
    LinearMap.det (LinearMap.mulRight ℝ g) = g.det ^ 2 := by
  classical

  let e : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
    (Matrix.ofLinearEquiv ℝ).symm.trans (LinearEquiv.piFinTwo ℝ (fun _ : Fin 2 => Fin 2 → ℝ))
  let T : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) := Matrix.toLin' g.transpose
  have hT : ∀ v : Fin 2 → ℝ, T v = Matrix.vecMul v g := fun v => by
    simp only [T, Matrix.toLin'_apply, Matrix.mulVec_transpose]
  have hrow : ∀ (X : Matrix (Fin 2) (Fin 2) ℝ) (i : Fin 2), (X * g) i = Matrix.vecMul (X i) g := by
    intro X i; funext j; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]
  have hconj : LinearMap.mulRight ℝ g = (e.symm : _ →ₗ[ℝ] _) ∘ₗ (LinearMap.prodMap T T) ∘ₗ (e.symm.symm : _ →ₗ[ℝ] _) := by
    apply LinearMap.ext
    intro X
    apply e.injective
    simp only [LinearMap.mulRight_apply, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply, LinearMap.prodMap_apply]
    refine Prod.ext ?_ ?_
    · show (X * g) 0 = T (X 0)
      rw [hT, hrow]
    · show (X * g) 1 = T (X 1)
      rw [hT, hrow]
  rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap]
  simp only [T, LinearMap.det_toLin', Matrix.det_transpose]
  ring

end MinkAux

open MinkAux in
theorem solution {a b : ℚ} (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ (C : Set (Matrix (Fin 2) (Fin 2) ℝ)) (S : Finset ℚ), IsCompact C ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ r ∈ R, r ≠ 0 ∧ nrd r ∈ S ∧
        ι r * (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ C := by
  classical

  have hsq : ∀ (y : ℍ[ℚ, a, b]), y ≠ 0 → y * y = 0 → False := by
    intro y hy hyy
    obtain ⟨u, rfl⟩ := hdiv y hy
    exact hy (by simpa using congrArg (fun z => (↑u⁻¹ : ℍ[ℚ, a, b]) * z) hyy)
  have ha : a ≠ 0 := by
    intro ha0
    refine hsq ⟨0, 1, 0, 0⟩ (by intro h; simpa using congrArg QuaternionAlgebra.imI h) ?_
    ext <;> simp [ha0]
  have hb : b ≠ 0 := by
    intro hb0
    refine hsq ⟨0, 0, 1, 0⟩ (by intro h; simpa using congrArg QuaternionAlgebra.imJ h) ?_
    ext <;> simp [hb0]

  obtain ⟨B₀, hB₀R, hB₀span⟩ := QuaternionAlgebra.IsOrder.exists_basis_span_eq hR
  let qi : ℍ[ℚ, a, b] := ⟨0, 1, 0, 0⟩
  let qj : ℍ[ℚ, a, b] := ⟨0, 0, 1, 0⟩
  have hqi : qi * qi = a • (1 : ℍ[ℚ, a, b]) := by ext <;> simp [qi]
  have hqj : qj * qj = b • (1 : ℍ[ℚ, a, b]) := by ext <;> simp [qj]
  have hqij : qi * qj = -(qj * qi) := by ext <;> simp [qi, qj]
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

  let v : Fin 4 → Matrix (Fin 2) (Fin 2) ℝ := fun n => ι (B₀ n)
  have hvspan : ∀ x : ℍ[ℚ, a, b], ι x ∈ Submodule.span ℝ (Set.range v) := by
    intro x
    have hx : x = ∑ n, (B₀.repr x) n • B₀ n := (B₀.sum_repr x).symm
    rw [hx, map_sum]
    refine Submodule.sum_mem _ fun n _ => ?_
    rw [map_smul, ← algebraMap_smul ℝ ((B₀.repr x) n) (ι (B₀ n))]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hind.span_eq_top_of_card_eq_finrank' hcard]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, rfl⟩
    fin_cases n
    · simpa using hvspan 1
    · simpa [hIdef] using hvspan qi
    · simpa [hJdef] using hvspan qj
    · simpa [hIdef, hJdef, map_mul] using hvspan (qi * qj)
  let bE : Module.Basis (Fin 4) ℝ (Matrix (Fin 2) (Fin 2) ℝ) := basisOfTopLeSpanOfCardEqFinrank v htop hcard
  have hbE : ∀ n, bE n = v n := fun n => by
    simp [bE, coe_basisOfTopLeSpanOfCardEqFinrank]

  let eL : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin 2 → Fin 2 → ℝ) := (Matrix.ofLinearEquiv ℝ).symm
  let bE' : Module.Basis (Fin 4) ℝ (Fin 2 → Fin 2 → ℝ) := bE.map eL
  have hbE' : ∀ n, bE' n = eL (v n) := fun n => by simp [bE', hbE]
  have hlat : ∀ x ∈ Submodule.span ℤ (Set.range ⇑bE'), ∃ r ∈ R, eL (ι r) = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, rfl⟩ := hy
      exact ⟨B₀ n, hB₀R n, (hbE' n).symm⟩
    | zero => exact ⟨0, R.zero_mem, by rw [map_zero, map_zero]⟩
    | add y z _ _ hy hz =>
      obtain ⟨r, hr, rfl⟩ := hy; obtain ⟨s, hs, rfl⟩ := hz
      exact ⟨r + s, R.add_mem hr hs, by rw [map_add, map_add]⟩
    | smul m y _ hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      exact ⟨m • r, R.smul_mem m hr, by rw [map_zsmul, map_zsmul]⟩
  let μ : Measure (Fin 2 → Fin 2 → ℝ) := Measure.addHaar
  haveI hCnt : Countable ↥(Submodule.span ℤ (Set.range ⇑bE')).toAddSubgroup := by
    change Countable ↥(Submodule.span ℤ (Set.range ⇑bE')); infer_instance
  have hF : IsAddFundamentalDomain (↥(Submodule.span ℤ (Set.range ⇑bE')).toAddSubgroup) (ZSpan.fundamentalDomain bE') μ :=
    ZSpan.isAddFundamentalDomain bE' μ
  have hFfin : μ (ZSpan.fundamentalDomain bE') < ⊤ := (ZSpan.fundamentalDomain_isBounded bE').measure_lt_top
  have hC1pos : 0 < μ (Metric.ball (0 : Fin 2 → Fin 2 → ℝ) 1) :=
    Metric.measure_ball_pos μ 0 one_pos
  have hfr : Module.finrank ℝ (Fin 2 → Fin 2 → ℝ) = 4 := by
    rw [Module.finrank_pi_fintype]; simp
  have h16 : μ (ZSpan.fundamentalDomain bE') * 2 ^ Module.finrank ℝ (Fin 2 → Fin 2 → ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top hFfin.ne (ENNReal.pow_ne_top (by simp))
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_mul_gt hC1pos.ne' h16
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · exfalso; rw [h0] at hn; simp at hn
    · exact hpos
  set ρ : ℝ := (n : ℝ) with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; exact_mod_cast Nat.zero_le n
  let C' : Set (Fin 2 → Fin 2 → ℝ) := Metric.closedBall 0 ρ
  have hCbig : μ (ZSpan.fundamentalDomain bE') * 2 ^ Module.finrank ℝ (Fin 2 → Fin 2 → ℝ) < μ C' := by
    refine hn.trans_le ?_
    show (n : ENNReal) * μ (Metric.ball 0 1) ≤ μ (Metric.closedBall 0 ρ)
    rw [Measure.addHaar_closedBall μ (0 : Fin 2 → Fin 2 → ℝ) hρ0, hfr]
    gcongr
    have : (n : ℝ) ≤ ρ ^ 4 := by
      rw [hρ]
      calc (n : ℝ) = (n : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (n : ℝ) ^ 4 := pow_le_pow_right₀ (by exact_mod_cast hn1) (by norm_num)
    calc (n : ENNReal) = ENNReal.ofReal (n : ℝ) := (ENNReal.ofReal_natCast n).symm
      _ ≤ ENNReal.ofReal (ρ ^ 4) := ENNReal.ofReal_le_ofReal this

  have heLc : Continuous (eL.symm : (Fin 2 → Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) :=
    LinearMap.continuous_of_finiteDimensional (eL.symm : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
  let C : Set (Matrix (Fin 2) (Fin 2) ℝ) := eL.symm '' C'
  have hCcpt : IsCompact C := (isCompact_closedBall (0 : Fin 2 → Fin 2 → ℝ) ρ).image heLc
  obtain ⟨Mb, hMb⟩ := hCcpt.exists_bound_of_continuousOn
    (f := fun X : Matrix (Fin 2) (Fin 2) ℝ => X.det) (continuous_id.matrix_det).continuousOn
  let N : ℕ := ⌈Mb⌉₊
  let S : Finset ℚ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).image (fun m : ℤ => (m : ℚ))
  refine ⟨C, S, hCcpt, fun g => ?_⟩

  let f : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → Fin 2 → ℝ) :=
    (eL : Matrix (Fin 2) (Fin 2) ℝ →ₗ[ℝ] (Fin 2 → Fin 2 → ℝ)) ∘ₗ
      (LinearMap.mulRight ℝ (g : Matrix (Fin 2) (Fin 2) ℝ)) ∘ₗ (eL.symm : (Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)
  have hfapp : ∀ y, f y = eL (eL.symm y * (g : Matrix (Fin 2) (Fin 2) ℝ)) := fun y => rfl
  have hdetf : LinearMap.det f = 1 := by
    have : f = (eL.symm.symm : _ →ₗ[ℝ] _) ∘ₗ (LinearMap.mulRight ℝ (g : Matrix (Fin 2) (Fin 2) ℝ)) ∘ₗ
        (eL.symm.symm.symm : _ →ₗ[ℝ] _) := by
      simp only [f, LinearEquiv.symm_symm]
    rw [this, LinearMap.det_conj, det_mulRight, Matrix.SpecialLinearGroup.det_coe, one_pow]
  have hpre : μ (f ⁻¹' C') = μ C' := by
    rw [Measure.addHaar_preimage_linearMap μ (by rw [hdetf]; exact one_ne_zero) C', hdetf]
    simp
  have hsymm : ∀ x ∈ f ⁻¹' C', -x ∈ f ⁻¹' C' := by
    intro x hx
    simp only [Set.mem_preimage, map_neg, C', Metric.mem_closedBall, dist_zero_right, norm_neg] at hx ⊢
    exact hx
  have hconv : Convex ℝ (f ⁻¹' C') := (convex_closedBall (0 : Fin 2 → Fin 2 → ℝ) ρ).linear_preimage f
  obtain ⟨⟨x, hxL⟩, hx0, hxC⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure hF hsymm hconv (by rw [hpre]; exact hCbig)
  obtain ⟨r, hrR, hrx⟩ := hlat x (by exact hxL)
  have hxC' : ι r * (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ C := by
    refine ⟨f x, by simpa using hxC, ?_⟩
    rw [hfapp, ← hrx, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  refine ⟨r, hrR, ?_, ?_, hxC'⟩
  · rintro rfl
    apply hx0
    ext1
    simp [← hrx]
  ·
    obtain ⟨m, hm⟩ := (QuaternionAlgebra.IsOrder.exists_intCast_eq_nrd_and_exists_intCast_eq_trd hR hrR).1
    have hdet : (ι r * (g : Matrix (Fin 2) (Fin 2) ℝ)).det = ((nrd r : ℚ) : ℝ) := by
      rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, mul_one, CerednikDrinfeld.det_map_eq_nrd ha hb ι hι]
    have hbd : |(m : ℝ)| ≤ Mb := by
      have := hMb _ hxC'
      rw [Real.norm_eq_abs, hdet, ← hm] at this
      exact_mod_cast this
    have hmN : |m| ≤ (N : ℤ) := by
      have h1 : ((|m| : ℤ) : ℝ) ≤ (⌈Mb⌉₊ : ℝ) := by
        have h2 : ((|m| : ℤ) : ℝ) ≤ Mb := by push_cast; exact hbd
        exact h2.trans (Nat.le_ceil Mb)
      exact_mod_cast h1
    rw [← hm]
    refine Finset.mem_image.2 ⟨m, ?_, rfl⟩
    rw [Finset.mem_Icc]
    exact abs_le.1 hmN

end S_CerednikDrinfeld_exists_isCompact_finset_forall_sl
end P2MW
export P2MW.S_CerednikDrinfeld_exists_isCompact_finset_forall_sl (solution)
