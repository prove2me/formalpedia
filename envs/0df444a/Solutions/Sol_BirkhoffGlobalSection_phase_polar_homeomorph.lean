-- Prove2me | solution 1 for BirkhoffGlobalSection.phase_polar_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:20:00.257983+00:00
-- url     : https://prove2.me/submissions/ef00c701-202c-4615-ab5a-85ce8be2096b

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.InnerProductSpace.PiL2

open BirkhoffGlobalSection Metric Set

noncomputable section

theorem solution :
    ∃ e : {s : Phase // s ≠ (fun _ : Fin 4 => (0 : ℝ))} ≃ₜ
      ({x : Phase // x ∈ unitThreeSphere} × {r : ℝ // 0 < r}),
      ∀ x : {x : Phase // x ∈ unitThreeSphere},
        ∀ r : {r : ℝ // 0 < r},
          ((e.symm (x, r) :
            {s : Phase // s ≠ (fun _ : Fin 4 => (0 : ℝ))}) : Phase) =
            (fun i : Fin 4 => (r : ℝ) * (x : Phase) i) := by
  let φ : Phase ≃ₜ EuclideanSpace ℝ (Fin 4) :=
    (EuclideanSpace.equiv (Fin 4) ℝ).symm.toHomeomorph
  have hφ (s : Phase) (i : Fin 4) : φ s i = s i := rfl
  have hnorm (s : Phase) : ‖φ s‖ ^ 2 = zNormSq s + wNormSq s := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_succ, hφ, zNormSq, wNormSq, Real.norm_eq_abs, sq_abs]
    ring
  have hzero (s : Phase) :
      s ≠ (fun _ : Fin 4 => (0 : ℝ)) ↔ φ s ≠ 0 := by
    have hz : φ (fun _ : Fin 4 => (0 : ℝ)) = 0 := by
      ext i
      simp [hφ]
    constructor
    · intro hn he
      exact hn (φ.injective (by simpa only [hz] using he))
    · intro hn he
      exact hn (by simpa only [hz] using congrArg φ he)
  have hsphere (s : Phase) :
      φ s ∈ sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 ↔ s ∈ unitThreeSphere := by
    rw [mem_sphere_zero_iff_norm]
    change ‖φ s‖ = 1 ↔ zNormSq s + wNormSq s = 1
    constructor
    · intro h
      rw [← hnorm, h]
      norm_num
    · intro h
      have hn : 0 ≤ ‖φ s‖ := norm_nonneg _
      nlinarith [hnorm s]
  let e₀ : {s : Phase // s ≠ (fun _ : Fin 4 => (0 : ℝ))} ≃ₜ
      {v : EuclideanSpace ℝ (Fin 4) // v ≠ 0} :=
    φ.subtype hzero
  let e₁ : {v : EuclideanSpace ℝ (Fin 4) // v ∈ sphere 0 1} ≃ₜ
      {s : Phase // s ∈ unitThreeSphere} :=
    φ.symm.subtype (by
      intro v
      simpa only [φ.apply_symm_apply] using (hsphere (φ.symm v)))
  let e := e₀.trans ((homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin 4))).trans
    (e₁.prodCongr (Homeomorph.refl {r : ℝ // 0 < r})))
  refine ⟨e, ?_⟩
  intro x r
  ext i
  change (e.symm (x, r) : Phase) i = _
  change (φ.symm ((r : ℝ) • φ (x : Phase))) i = _
  change ((EuclideanSpace.equiv (Fin 4) ℝ) ((r : ℝ) • φ (x : Phase))) i = _
  rw [map_smul]
  simp [φ, Pi.smul_apply, smul_eq_mul]
