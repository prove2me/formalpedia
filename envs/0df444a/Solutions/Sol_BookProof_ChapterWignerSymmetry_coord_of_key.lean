-- Prove2me | solution 1 for BookProof.ChapterWignerSymmetry.coord_of_key
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T09:58:54.422479+00:00
-- url     : https://prove2.me/submissions/c1361b77-7f41-461a-95ea-3a17d5f80aee

-- Generated from ChapterWignerSymmetry.lean — solution of BookProof.ChapterWignerSymmetry.coord_of_key
import Mathlib
import Definitions.Def_ChapterWignerSymmetry
import Theorems.Thm_BookProof_ChapterWignerSymmetry_eq_norm_of_re_eq_norm
import Theorems.Thm_BookProof_ChapterWignerSymmetry_S_zero
import Theorems.Thm_BookProof_ChapterWignerSymmetry_coord_of_key_of_ne_zero
import Definitions.Def_ChapterWignerSymmetryInfinite
open BookProof.ChapterWignerSymmetry



open scoped InnerProductSpace ComplexConjugate
open Finset


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]


variable {T : E → E}

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {T : E → E}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : (ι → ℂ) → (ι → ℂ)} {o : ι}

set_option maxHeartbeats 1000000 in
theorem solution (hS : WignerCoord S o) (κ : ℂ →+* ℂ) (hκn : ∀ z, ‖κ z‖ = ‖z‖)
    (hκc : ∀ z, κ (conj z) = conj (κ z))
    (hkey : ∀ i, i ≠ o → ∀ v, conj (S v o) * S v i = κ (conj (v o) * v i)) (v : ι → ℂ) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ ∀ k, S v k = lam * κ (v k) := by

  by_cases hvo : v o = 0
  · have hSvo : S v o = 0 := S_zero hS hvo
    by_cases hzero : ∀ k, v k = 0
    · refine ⟨1, by norm_num, fun k => ?_⟩
      rw [hzero k, κ.map_zero, mul_zero]
      exact S_zero hS (hzero k)
    · push_neg at hzero
      obtain ⟨k₀, hk₀⟩ := hzero
      set y : ι → ℂ := fun k => if k = o then 1 else v k with hy
      have hyo : y o = 1 := by simp [hy]
      have hyk : ∀ k, k ≠ o → y k = v k := by intro k hk; simp [hy, hk]
      obtain ⟨μ, hμ, hμeq⟩ :=
        coord_of_key_of_ne_zero hS κ hκn hκc hkey (v := y) (by rw [hyo]; norm_num)
      set M : ℝ := ∑ k, ‖v k‖ ^ 2 with hMdef
      set Z : ℂ := ∑ k, conj (κ (v k)) * S v k with hZdef
      have hMpos : 0 < M := by
        rw [hMdef]
        refine Finset.sum_pos' (fun k _ => by positivity) ⟨k₀, Finset.mem_univ _, ?_⟩
        have : ‖v k₀‖ ≠ 0 := by simpa using hk₀
        positivity
      -- the two sides of the invariance relation
      have hsum1 : ∑ k, conj (S y k) * S v k = conj μ * Z := by
        rw [hZdef, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hμeq k, map_mul]
        by_cases hk : k = o
        · subst hk
          simp [hSvo]
        · rw [hyk k hk]
          ring
      have hsum2 : ∑ k, conj (y k) * v k = ((M : ℝ) : ℂ) := by
        rw [hMdef]
        push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = o
        · subst hk
          simp [hyo, hvo]
        · rw [hyk k hk, mul_comm, Complex.mul_conj]
          norm_cast
          rw [Complex.sq_norm]
      have hZnorm : ‖Z‖ = M := by
        have h := hS.inner_norm y v
        rw [hsum1, hsum2, norm_mul, Complex.norm_conj, hμ, one_mul,
          Complex.norm_real, Real.norm_of_nonneg hMpos.le] at h
        exact h
      -- equality in the triangle inequality
      have hZne : Z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hZnorm
        exact absurd hZnorm.symm (ne_of_gt hMpos)
      refine ⟨Z / ((M : ℝ) : ℂ), ?_, ?_⟩
      · rw [norm_div, hZnorm, Complex.norm_real, Real.norm_of_nonneg hMpos.le,
          div_self (ne_of_gt hMpos)]
      · set lam : ℂ := Z / ((M : ℝ) : ℂ) with hlamdef
        have hMC : ((M : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hMpos
        have hlamnorm : ‖lam‖ = 1 := by
          rw [hlamdef, norm_div, hZnorm, Complex.norm_real, Real.norm_of_nonneg hMpos.le,
            div_self (ne_of_gt hMpos)]
        have hlamconj : lam * conj lam = 1 := by
          rw [Complex.mul_conj]
          have hsq : Complex.normSq lam = ‖lam‖ ^ 2 := by rw [Complex.sq_norm]
          rw [hsq, hlamnorm]; norm_num
        have hsumt : ∑ k, conj lam * (conj (κ (v k)) * S v k) = ((M : ℝ) : ℂ) := by
          rw [← Finset.mul_sum, ← hZdef, hlamdef, map_div₀]
          rw [Complex.conj_ofReal]
          field_simp
          rw [mul_comm, Complex.mul_conj]
          have hsq : Complex.normSq Z = ‖Z‖ ^ 2 := by rw [Complex.sq_norm]
          rw [hsq, hZnorm]
          push_cast
          ring
        have hle : ∀ k ∈ Finset.univ,
            (conj lam * (conj (κ (v k)) * S v k)).re ≤ ‖v k‖ ^ 2 := by
          intro k _
          have h1 : ‖conj lam * (conj (κ (v k)) * S v k)‖ = ‖v k‖ ^ 2 := by
            rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hlamnorm, hκn,
              hS.coord_norm v k, one_mul]
            ring
          calc (conj lam * (conj (κ (v k)) * S v k)).re
              ≤ ‖conj lam * (conj (κ (v k)) * S v k)‖ := Complex.re_le_norm _
            _ = ‖v k‖ ^ 2 := h1
        have hsumre : ∑ k, (conj lam * (conj (κ (v k)) * S v k)).re = ∑ k, ‖v k‖ ^ 2 := by
          rw [← Complex.re_sum, hsumt, Complex.ofReal_re, hMdef]
        have hterm := (Finset.sum_eq_sum_iff_of_le hle).1 hsumre
        intro k
        have hk := hterm k (Finset.mem_univ k)
        by_cases hvk : v k = 0
        · rw [hvk, κ.map_zero, mul_zero]
          exact S_zero hS hvk
        · have hnorm : ‖conj lam * (conj (κ (v k)) * S v k)‖ = ‖v k‖ ^ 2 := by
            rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hlamnorm, hκn,
              hS.coord_norm v k, one_mul]
            ring
          have hreal : conj lam * (conj (κ (v k)) * S v k) = ((‖v k‖ ^ 2 : ℝ) : ℂ) := by
            have := eq_norm_of_re_eq_norm (z := conj lam * (conj (κ (v k)) * S v k))
              (by rw [hk, hnorm])
            rw [this, hnorm]
          have hκvk : κ (v k) ≠ 0 := by
            intro h
            apply hvk
            have := hκn (v k)
            rw [h] at this
            simpa [eq_comm] using this.symm
          have hne : conj (κ (v k)) ≠ 0 := by simpa using hκvk
          have hprod : conj (κ (v k)) * κ (v k) = ((‖v k‖ ^ 2 : ℝ) : ℂ) := by
            rw [mul_comm, Complex.mul_conj]
            have hsq : Complex.normSq (κ (v k)) = ‖κ (v k)‖ ^ 2 := by rw [Complex.sq_norm]
            rw [hsq, hκn]
          have hcancel : conj lam * S v k = κ (v k) := by
            refine mul_left_cancel₀ hne ?_
            calc conj (κ (v k)) * (conj lam * S v k)
                = conj lam * (conj (κ (v k)) * S v k) := by ring
              _ = ((‖v k‖ ^ 2 : ℝ) : ℂ) := hreal
              _ = conj (κ (v k)) * κ (v k) := hprod.symm
          calc S v k = (lam * conj lam) * S v k := by rw [hlamconj]; ring
            _ = lam * (conj lam * S v k) := by ring
            _ = lam * κ (v k) := by rw [hcancel]
  · exact coord_of_key_of_ne_zero hS κ hκn hκc hkey hvo
