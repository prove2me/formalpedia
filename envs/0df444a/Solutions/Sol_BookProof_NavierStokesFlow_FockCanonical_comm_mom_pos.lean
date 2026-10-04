-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.comm_mom_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:10:08.394339+00:00
-- url     : https://prove2.me/submissions/e8513922-63c7-4b35-ada9-7108e742dc75

import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Definitions.Def_ChapterBosonicCCR
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesAffineFiberEsa

set_option autoImplicit false

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
  BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.FockManyMode in
theorem p764_ann_cre_comm {d : ℕ} (i : Fin d) :
    FockCanonical.ann i * FockCanonical.cre i - FockCanonical.cre i * FockCanonical.ann i
      = (1 : Module.End ℂ (lpFiniteModes (Occ d))) := by
  apply LinearMap.ext
  intro x
  refine Subtype.ext (lp.ext (funext fun α => ?_))
  have hA : ∀ (y : lpFiniteModes (Occ d)) (β : Occ d),
      (((FockCanonical.ann i y : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) β
        = (Real.sqrt ((β i : ℝ) + 1) : ℂ) * ((y : L2I (Occ d)) : Occ d → ℂ) (FockCanonical.up i β) :=
    fun _ _ => rfl
  have hC : ∀ (y : lpFiniteModes (Occ d)) (β : Occ d),
      (((FockCanonical.cre i y : lpFiniteModes (Occ d)) : L2I (Occ d)) : Occ d → ℂ) β
        = (Real.sqrt (β i : ℝ) : ℂ) * ((y : L2I (Occ d)) : Occ d → ℂ) (FockCanonical.dn i β) :=
    fun _ _ => rfl
  simp only [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply,
    Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply]
  rw [hA, hC, hC, hA]
  have hup : (FockCanonical.up i α) i = α i + 1 := by simp [FockCanonical.up]
  have hdu : FockCanonical.dn i (FockCanonical.up i α) = α := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [FockCanonical.up, FockCanonical.dn]
    · simp [FockCanonical.up, FockCanonical.dn, hj]
  rw [hup, hdu]
  set X := ((x : L2I (Occ d)) : Occ d → ℂ)
  have h1 : (Real.sqrt ((α i : ℝ) + 1) : ℂ) * (Real.sqrt (((α i + 1 : ℕ)) : ℝ) : ℂ)
      = ((α i : ℝ) + 1 : ℝ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    push_cast
    exact Real.mul_self_sqrt (by positivity)
  rcases Nat.eq_zero_or_pos (α i) with h0 | hpos
  · rw [← mul_assoc, h1, h0]
    simp
  · have hdn : (FockCanonical.dn i α) i = α i - 1 := by simp [FockCanonical.dn]
    have hud : FockCanonical.up i (FockCanonical.dn i α) = α :=
      FockCanonical.up_dn i (by omega)
    rw [hdn, hud]
    have h2 : (Real.sqrt (α i : ℝ) : ℂ) * (Real.sqrt (((α i - 1 : ℕ) : ℝ) + 1) : ℂ)
        = (α i : ℝ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      have : (((α i - 1 : ℕ) : ℝ) + 1) = (α i : ℝ) := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]
      exact Real.mul_self_sqrt (by positivity)
    rw [← mul_assoc, h1, ← mul_assoc, h2]
    push_cast
    ring

theorem p764_alg {R : Type*} [Ring R] [Algebra ℂ R] (A C : R) (h : A * C - C * A = 1) (a b : ℂ) :
    (a • (C - A)) * (b • (C + A)) - (b • (C + A)) * (a • (C - A)) = (-2 * a * b) • (1 : R) := by
  have e : (C - A) * (C + A) - (C + A) * (C - A) = -((A * C - C * A) + (A * C - C * A)) := by
    simp only [sub_mul, mul_sub, add_mul, mul_add]; abel
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm b a, ← smul_sub, e, h]
  module

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockCanonical in
theorem solution {d : ℕ} {κ : Fin d → ℝ} (i : Fin d) (hκ : 0 < κ i) :
    (mom κ i).comp (pos κ i) - (pos κ i).comp (mom κ i) = (-Complex.I) • LinearMap.id := by
  have hcomm := p764_ann_cre_comm (d := d) i
  set A := FockCanonical.ann (d := d) i
  set C := FockCanonical.cre (d := d) i
  set s := Real.sqrt (κ i / 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hss : s * s = κ i / 2 := Real.mul_self_sqrt (by linarith)
  have h2 : Real.sqrt (2 * κ i) = 2 * s := by
    rw [show 2 * κ i = (2 * s) * (2 * s) by nlinarith]
    exact Real.sqrt_mul_self (by linarith)
  have hmom : mom κ i = (Complex.I * (s : ℂ)) • (C - A) := rfl
  have hpos : pos κ i = ((1 / (2 * s) : ℝ) : ℂ) • (C + A) := by
    show ((1 / Real.sqrt (2 * κ i) : ℝ) : ℂ) • (C + A) = _
    rw [h2]
  have key := p764_alg A C hcomm (Complex.I * (s : ℂ)) ((1 / (2 * s) : ℝ) : ℂ)
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hmom, hpos]
  refine key.trans ?_
  rw [← Module.End.one_eq_id]
  congr 1
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  push_cast
  field_simp
