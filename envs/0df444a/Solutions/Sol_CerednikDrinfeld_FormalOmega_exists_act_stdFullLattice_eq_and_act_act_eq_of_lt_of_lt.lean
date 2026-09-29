-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a4cae8ce-f701-5b7d-bc5c-c59ef278a6df

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Theorems.Thm_LT_LatticeTree_exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt

set_option autoImplicit false

open scoped TensorProduct
p2m_open "LT.LatticeTree CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt.CerednikDrinfeld.FormalOmega"

open scoped Matrix

namespace CerednikDrinfeld
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "stdFullLattice FullLattice.act"
namespace EdgeTransAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open LT.LatticeTree

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]

theorem coords_of_mem_stdLattice {v : Fin 2 → K} (hv : v ∈ stdLattice 𝒪 K) :
    ∃ x y : 𝒪, algebraMap 𝒪 K x = v 0 ∧ algebraMap 𝒪 K y = v 1 := by
  obtain ⟨x, hx⟩ := ((mem_stdLattice 𝒪 K).1 hv) 0
  obtain ⟨y, hy⟩ := ((mem_stdLattice 𝒪 K).1 hv) 1
  exact ⟨x, y, hx, hy⟩

theorem isUnit_of_not_dvd {π : 𝒪} (hπ : Irreducible π) {a : 𝒪} (h : ¬ π ∣ a) : IsUnit a := by
  by_contra hu
  apply h
  have : a ∈ IsLocalRing.maximalIdeal 𝒪 := (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hu)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ] at this
  exact Ideal.mem_span_singleton.1 this

theorem latticeMap_diag_stdLattice {π : 𝒪} (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1]) :
    latticeMap g (stdLattice 𝒪 K) = interLattice 𝒪 K π 0 1 := by
  ext v
  rw [mem_latticeMap, mem_interLattice]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hw' := (mem_stdLattice 𝒪 K).1 hw
    have h0 : ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 0 = algebraMap 𝒪 K π * w 0 := by
      rw [hg, Matrix.mulVec_diagonal]; simp
    have h1 : ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) 1 = w 1 := by
      rw [hg, Matrix.mulVec_diagonal]; simp
    refine ⟨?_, w 0, hw' 0, ?_⟩
    · refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
      · rw [h0]; exact IsLocalization.isInteger_mul ⟨π, rfl⟩ (hw' 0)
      · rw [h1]; exact hw' 1
    · rw [h0, h1, map_one, map_zero, one_mul, zero_mul, sub_zero]
  · rintro ⟨hv, w, hw, hvw⟩
    rw [map_one, map_zero, one_mul, zero_mul, sub_zero] at hvw
    refine ⟨![w, v 1], ?_, ?_⟩
    · rw [mem_stdLattice]
      intro i
      fin_cases i
      · simpa using hw
      · simpa using hv 1
    · rw [hg]
      funext i
      rw [Matrix.mulVec_diagonal]
      fin_cases i
      · simp [hvw]
      · simp

theorem latticeMap_map_stdLattice (π : 𝒪) (M : Matrix.GeneralLinearGroup (Fin 2) 𝒪) :
    latticeMap (Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M) (stdLattice 𝒪 K) = stdLattice 𝒪 K := by
  rw [← interLattice_zero_zero (R := 𝒪) (K := K) π, latticeMap_map_interLattice]
  simp

theorem exists_eq_interLattice {π : 𝒪} (hπ : Irreducible π) {L : Submodule 𝒪 (Fin 2 → K)}
    (h₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) < L)
    (h₂ : L < stdLattice 𝒪 K) :
    ∃ a b : 𝒪, (IsUnit a ∨ IsUnit b) ∧ L = interLattice 𝒪 K π a b := by
  obtain ⟨-, v, hvL, hvπ⟩ := SetLike.lt_iff_le_and_exists.1 h₁
  have hvstd : v ∈ stdLattice 𝒪 K := h₂.le hvL
  obtain ⟨a, b, ha, hb⟩ := coords_of_mem_stdLattice hvstd

  have hunit : IsUnit a ∨ IsUnit b := by
    by_contra hne
    push Not at hne
    obtain ⟨hna, hnb⟩ := hne
    apply hvπ
    rw [mem_latticeMap_scalarGL_stdLattice hπ.ne_zero]
    have hda : π ∣ a := by by_contra h; exact hna (isUnit_of_not_dvd hπ h)
    have hdb : π ∣ b := by by_contra h; exact hnb (isUnit_of_not_dvd hπ h)
    obtain ⟨a', rfl⟩ := hda
    obtain ⟨b', rfl⟩ := hdb
    intro i
    fin_cases i
    · exact ⟨algebraMap 𝒪 K a', ⟨a', rfl⟩, by rw [← map_mul]; exact ha⟩
    · exact ⟨algebraMap 𝒪 K b', ⟨b', rfl⟩, by rw [← map_mul]; exact hb⟩
  refine ⟨a, b, hunit, le_antisymm ?_ ?_⟩
  ·
    intro u hu
    by_contra huI
    have hustd : u ∈ stdLattice 𝒪 K := h₂.le hu
    obtain ⟨x, y, hx, hy⟩ := coords_of_mem_stdLattice hustd
    have hndvd : ¬ π ∣ b * x - a * y := by
      intro hd
      apply huI
      obtain ⟨w, hw, hweq⟩ := (exists_isInteger_eq_algebraMap_mul_iff_dvd (K := K)).2 hd
      refine ⟨(mem_stdLattice 𝒪 K).1 hustd, w, hw, ?_⟩
      rw [← hx, ← hy, ← map_mul, ← map_mul, ← map_sub]
      exact hweq
    obtain ⟨δ, hδ⟩ := isUnit_of_not_dvd hπ hndvd
    have hδinv : (b * x - a * y) * ((δ⁻¹ : 𝒪ˣ) : 𝒪) = 1 := by rw [← hδ, Units.mul_inv]

    have hstd : stdLattice 𝒪 K ≤ L := by
      intro s hs
      obtain ⟨σ₀, σ₁, hσ₀, hσ₁⟩ := coords_of_mem_stdLattice hs
      set lam : 𝒪 := -(σ₀ * y - σ₁ * x) * ((δ⁻¹ : 𝒪ˣ) : 𝒪) with hlam
      set mu : 𝒪 := (b * σ₀ - a * σ₁) * ((δ⁻¹ : 𝒪ˣ) : 𝒪) with hmu
      have hcomb : s = lam • v + mu • u := by
        funext i
        rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]
        fin_cases i
        · show s 0 = algebraMap 𝒪 K lam * v 0 + algebraMap 𝒪 K mu * u 0
          rw [← hσ₀, ← ha, ← hx, ← map_mul, ← map_mul, ← map_add]
          congr 1
          rw [hlam, hmu]
          linear_combination (-σ₀) * hδinv
        · show s 1 = algebraMap 𝒪 K lam * v 1 + algebraMap 𝒪 K mu * u 1
          rw [← hσ₁, ← hb, ← hy, ← map_mul, ← map_mul, ← map_add]
          congr 1
          rw [hlam, hmu]
          linear_combination (-σ₁) * hδinv
      rw [hcomb]
      exact L.add_mem (L.smul_mem lam hvL) (L.smul_mem mu hu)
    exact absurd (le_antisymm h₂.le hstd) h₂.ne
  ·
    rintro u ⟨hu, w, hw, hwu⟩
    obtain ⟨x, y, hx, hy⟩ := coords_of_mem_stdLattice ((mem_stdLattice 𝒪 K).2 hu)
    obtain ⟨ω, rfl⟩ := hw
    rw [← hx, ← hy, ← map_mul, ← map_mul, ← map_sub, ← map_mul] at hwu
    have hwu' : b * x - a * y = π * ω := IsFractionRing.injective 𝒪 K hwu
    have hπL : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) ≤ L := h₁.le

    have key : ∀ t r₀ r₁ : 𝒪, x - t * a = π * r₀ → y - t * b = π * r₁ → u ∈ L := by
      intro t r₀ r₁ h0 h1
      have hr : u - t • v ∈ latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) := by
        rw [mem_latticeMap_scalarGL_stdLattice hπ.ne_zero]
        intro i
        fin_cases i
        · refine ⟨algebraMap 𝒪 K r₀, ⟨r₀, rfl⟩, ?_⟩
          show algebraMap 𝒪 K π * algebraMap 𝒪 K r₀ = (u - t • v) 0
          rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def, ← hx, ← ha, ← map_mul, ← map_mul, ← map_sub, ← h0]
        · refine ⟨algebraMap 𝒪 K r₁, ⟨r₁, rfl⟩, ?_⟩
          show algebraMap 𝒪 K π * algebraMap 𝒪 K r₁ = (u - t • v) 1
          rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def, ← hy, ← hb, ← map_mul, ← map_mul, ← map_sub, ← h1]
      have : u = t • v + (u - t • v) := by abel
      rw [this]
      exact L.add_mem (L.smul_mem t hvL) (hπL hr)
    rcases hunit with ⟨ai, hai⟩ | ⟨bi, hbi⟩
    · have hinv : ((ai⁻¹ : 𝒪ˣ) : 𝒪) * a = 1 := by rw [← hai, Units.inv_mul]
      refine key (x * ((ai⁻¹ : 𝒪ˣ) : 𝒪)) 0 (-(((ai⁻¹ : 𝒪ˣ) : 𝒪) * ω)) ?_ ?_
      · linear_combination (-x) * hinv
      · linear_combination (-(((ai⁻¹ : 𝒪ˣ) : 𝒪))) * hwu' + (-y) * hinv
    · have hinv : ((bi⁻¹ : 𝒪ˣ) : 𝒪) * b = 1 := by rw [← hbi, Units.inv_mul]
      refine key (y * ((bi⁻¹ : 𝒪ˣ) : 𝒪)) (((bi⁻¹ : 𝒪ˣ) : 𝒪) * ω) 0 ?_ ?_
      · linear_combination (((bi⁻¹ : 𝒪ˣ) : 𝒪)) * hwu' + (-x) * hinv
      · linear_combination (-y) * hinv

theorem exists_gl_snd_col {a b : 𝒪} (h : IsUnit a ∨ IsUnit b) :
    ∃ M : Matrix.GeneralLinearGroup (Fin 2) 𝒪, (M : Matrix (Fin 2) (Fin 2) 𝒪) 0 1 = a ∧ (M : Matrix (Fin 2) (Fin 2) 𝒪) 1 1 = b := by
  rcases h with ha | hb
  · have hdet : IsUnit (!![0, a; -1, b] : Matrix (Fin 2) (Fin 2) 𝒪).det := by
      rw [Matrix.det_fin_two_of]; simpa using ha
    obtain ⟨M, hM⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
    exact ⟨M, by rw [hM]; rfl, by rw [hM]; rfl⟩
  · have hdet : IsUnit (!![1, a; 0, b] : Matrix (Fin 2) (Fin 2) 𝒪).det := by
      rw [Matrix.det_fin_two_of]; simpa using hb
    obtain ⟨M, hM⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
    exact ⟨M, by rw [hM]; rfl, by rw [hM]; rfl⟩

end CerednikDrinfeld.FormalOmega.EdgeTransAux

open CerednikDrinfeld.FormalOmega.EdgeTransAux in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K]
    (π : 𝒪) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (hg : (g : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal ![algebraMap 𝒪 K π, 1])
    (M' M : FullLattice 𝒪 K)
    (h₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) M.1 < M'.1) (h₂ : M'.1 < M.1) :
    ∃ h : Matrix.GeneralLinearGroup (Fin 2) K,
      FullLattice.act h (stdFullLattice K) = M ∧ FullLattice.act h (FullLattice.act g (stdFullLattice K)) = M' := by

  obtain ⟨c, n, β, g₁, -, hM⟩ :=
    LT.LatticeTree.exists_eq_latticeMap_scalarGL_mul_triangular_stdLattice 𝒪 K π hπ M.1 M.2
  set k : Matrix.GeneralLinearGroup (Fin 2) K := scalarGL c * g₁ with hk
  set L : Submodule 𝒪 (Fin 2 → K) := latticeMap k⁻¹ M'.1 with hL
  have hπk : ∀ N : Submodule 𝒪 (Fin 2 → K),
      latticeMap k⁻¹ (latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) N) =
        latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (latticeMap k⁻¹ N) := by
    intro N; rw [← latticeMap_mul, ← scalarGL_mul_comm, latticeMap_mul]
  have hL₁ : latticeMap (scalarGL (unitOfNeZero (K := K) hπ.ne_zero)) (stdLattice 𝒪 K) < L := by
    have := (latticeMap_lt_latticeMap_iff k⁻¹).2 h₁
    rwa [hπk, hM, latticeMap_inv_latticeMap] at this
  have hL₂ : L < stdLattice 𝒪 K := by
    have := (latticeMap_lt_latticeMap_iff k⁻¹).2 h₂
    rwa [hM, latticeMap_inv_latticeMap] at this

  obtain ⟨a, b, hab, hLI⟩ := exists_eq_interLattice hπ hL₁ hL₂

  obtain ⟨M₀, h01, h11⟩ := exists_gl_snd_col hab
  have hM₀I : latticeMap (Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M₀) (interLattice 𝒪 K π 0 1) =
      interLattice 𝒪 K π a b := by
    rw [latticeMap_map_interLattice]
    simp [h01, h11]
  refine ⟨k * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M₀, Subtype.ext ?_, Subtype.ext ?_⟩
  · show latticeMap (k * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M₀) (stdLattice 𝒪 K) = M.1
    rw [latticeMap_mul, latticeMap_map_stdLattice π, hM]
  · show latticeMap (k * Matrix.GeneralLinearGroup.map (algebraMap 𝒪 K) M₀) (latticeMap g (stdLattice 𝒪 K)) = M'.1
    rw [latticeMap_mul, latticeMap_diag_stdLattice g hg, hM₀I, ← hLI, hL, latticeMap_latticeMap_inv]

end S_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_exists_act_stdFullLattice_eq_and_act_act_eq_of_lt_of_lt (solution)
