-- Prove2me | solution 1 for BookProof.HermiteCarleman.shifted_faces_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:31:22.806208+00:00
-- url     : https://prove2.me/submissions/e7254335-540a-4b9a-b6d9-b9d34dc5f44f

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.shifted_faces_le
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteCarleman



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ} {lam : (Fin d →₀ ℕ) → ℝ} {amp : Fin d → ℂ} {z : ℂ}

namespace S79HC

theorem mem_cube' {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ cube d N ↔ ∀ i, a i ≤ N := by
  unfold cube
  simp only [Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨f, hf, rfl⟩ i
    simpa using Nat.lt_succ_iff.mp (hf i)
  · intro h
    exact ⟨Finsupp.equivFunOnFinite a, fun i => Nat.lt_succ_of_le (by simpa using h i), by simp⟩

theorem mem_inn' {d N : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} :
    a ∈ inn d N i ↔ (∀ j, a j ≤ N) ∧ a i < N := by
  unfold inn; rw [Finset.mem_filter, mem_cube']

theorem mem_face' {d N : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} :
    a ∈ face d N i ↔ (∀ j, a j ≤ N) ∧ a i = N := by
  unfold face; rw [Finset.mem_filter, mem_cube']

theorem sum_shift (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ)
    (hF : ∀ a : Fin d →₀ ℕ, a i = 0 → F a = 0) :
    ∑ a ∈ cube d N, F a = ∑ b ∈ inn d N i, F (b + Finsupp.single i 1) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun a => a i ≠ 0)
    (fun a _ h => fun h0 => h (hF a h0))]
  apply Finset.sum_nbij' (fun a => a - Finsupp.single i 1) (fun b => b + Finsupp.single i 1)
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_coe, mem_cube', mem_inn'] at ha ⊢
    refine ⟨fun j => ?_, ?_⟩
    · have := ha.1 j; simp only [Finsupp.coe_tsub, Pi.sub_apply]; omega
    · have := ha.1 i; simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_coe, mem_cube', mem_inn'] at hb ⊢
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hj, hb.1 j]
    · simp
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_coe] at ha
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  · intro b _
    simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    congr 1
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hj]


theorem lterm_shift (i : Fin d) (b : Fin d →₀ ℕ) :
    lterm u amp i (b + Finsupp.single i 1) = (starRingEnd ℂ) (rterm u amp i b) := by
  unfold lterm rterm
  simp only [add_tsub_cancel_right, Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
    map_mul, Complex.conj_conj, Complex.conj_ofReal, Nat.cast_add, Nat.cast_one]
  ring

theorem sum_lterm (N : ℕ) (i : Fin d) :
    ∑ a ∈ cube d N, lterm u amp i a
      = (starRingEnd ℂ) (∑ a ∈ inn d N i, rterm u amp i a) := by
  rw [sum_shift d N i _ (fun a ha => by simp [lterm, ha]), map_sum]
  exact Finset.sum_congr rfl (fun b _ => lterm_shift i b)

theorem sum_range_of_disjoint {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (G : ℕ → Finset (Fin d →₀ ℕ)) (hd : ∀ M N : ℕ, M ≠ N → Disjoint (G M) (G N)) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2 ≤ B := by
  classical
  rw [← Finset.sum_biUnion (fun x _ y _ h => hd x y h)]
  exact hbes _

theorem faces_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ face d N i, ‖u a‖ ^ 2 ≤ B := by
  refine sum_range_of_disjoint hbes (fun N => face d N i) (fun M N h => ?_) M
  rw [Finset.disjoint_left]
  intro a h1 h2
  rw [mem_face'] at h1 h2
  exact h (h1.2.symm.trans h2.2)

theorem shifted_faces_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ face d N i, ‖u (a + Finsupp.single i 1)‖ ^ 2 ≤ B := by
  classical
  have h := sum_range_of_disjoint hbes
    (fun N => (face d N i).image (· + Finsupp.single i 1)) (fun M N h => ?_) M
  · refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl (fun N _ => ?_)
    rw [Finset.sum_image (fun x _ y _ hxy => add_right_cancel hxy)]
  · rw [Finset.disjoint_left]
    intro a h1 h2
    simp only [Finset.mem_image, mem_face'] at h1 h2
    obtain ⟨x, hx, rfl⟩ := h1
    obtain ⟨y, hy, hxy⟩ := h2
    have := congrArg (fun f => f i) hxy
    simp at this
    omega

theorem not_summable_inv_sqrt : ¬ Summable (fun N : ℕ => (Real.sqrt ((N : ℝ) + 1))⁻¹) := by
  intro hs
  have h2 : Summable (fun N : ℕ => (((N + 1 : ℕ) : ℝ))⁻¹) := by
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hs
    push_cast
    have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [N.cast_nonneg (α := ℝ)]
    apply inv_anti₀ (Real.sqrt_pos.mpr (by linarith))
    calc Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1) :=
          le_mul_of_one_le_right (Real.sqrt_nonneg _) (by rw [Real.one_le_sqrt]; exact h1)
      _ = (N : ℝ) + 1 := Real.mul_self_sqrt (by linarith)
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp h2)

theorem flux_bound (N : ℕ) (i : Fin d) :
    |(∑ a ∈ face d N i, rterm u amp i a).im|
      ≤ Real.sqrt ((N : ℝ) + 1) *
        (‖amp i‖ * ((∑ a ∈ face d N i,
          (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i 1)‖ ^ 2)) / 2)) := by
  calc |(∑ a ∈ face d N i, rterm u amp i a).im|
      ≤ ‖∑ a ∈ face d N i, rterm u amp i a‖ := Complex.abs_im_le_norm _
    _ ≤ ∑ a ∈ face d N i, ‖rterm u amp i a‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ face d N i, Real.sqrt ((N : ℝ) + 1) *
          (‖amp i‖ * ((‖u a‖ ^ 2 + ‖u (a + Finsupp.single i 1)‖ ^ 2) / 2)) := by
        apply Finset.sum_le_sum
        intro a ha
        rw [mem_face'] at ha
        unfold rterm
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg (Real.sqrt_nonneg _), ha.2]
        have h1 : ‖u a‖ * ‖u (a + Finsupp.single i 1)‖ ≤
            (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i 1)‖ ^ 2) / 2 := by
          nlinarith [sq_nonneg (‖u a‖ - ‖u (a + Finsupp.single i 1)‖)]
        have h2 := mul_le_mul_of_nonneg_left h1
          (mul_nonneg (norm_nonneg (amp i)) (Real.sqrt_nonneg ((N : ℝ) + 1)))
        nlinarith [h2]
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_div]

end S79HC

theorem solution {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ face d N i, ‖u (a + Finsupp.single i 1)‖ ^ 2 ≤ B := by
  apply S79HC.shifted_faces_le <;> assumption
