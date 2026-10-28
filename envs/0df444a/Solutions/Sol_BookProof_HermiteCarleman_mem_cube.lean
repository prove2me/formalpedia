-- Prove2me | solution 1 for BookProof.HermiteCarleman.mem_cube
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:32:06.231963+00:00
-- url     : https://prove2.me/submissions/5cb3d459-0d4e-48f4-bf44-935844c0586b

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.mem_cube
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

theorem h_mem_cube {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ cube d N ↔ ∀ i, a i ≤ N := by
  unfold cube
  simp only [Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨f, hf, rfl⟩ i
    simpa using Nat.lt_succ_iff.mp (hf i)
  · intro h
    exact ⟨Finsupp.equivFunOnFinite a, fun i => by simpa using Nat.lt_succ_of_le (h i), by simp⟩

theorem h_mem_face {d N : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} :
    a ∈ face d N i ↔ (∀ j, a j ≤ N) ∧ a i = N := by
  unfold face; rw [Finset.mem_filter, h_mem_cube]

theorem h_mem_inn {d N : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} :
    a ∈ inn d N i ↔ (∀ j, a j ≤ N) ∧ a i < N := by
  unfold inn; rw [Finset.mem_filter, h_mem_cube]

theorem h_sub_add_single {d : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} (h : a i ≠ 0) :
    (a - Finsupp.single i 1) + Finsupp.single i 1 = a := by
  ext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [Finsupp.single_apply, Ne.symm hj]

theorem h_not_summable : ¬ Summable (fun N : ℕ => (Real.sqrt ((N : ℝ) + 1))⁻¹) := by
  intro hs
  have h2 : Summable (fun N : ℕ => (1 : ℝ) / ((N + 1 : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hs
    have h1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by have := N.cast_nonneg (α := ℝ); linarith
    have hs1 : Real.sqrt ((N : ℝ) + 1) ≤ (N : ℝ) + 1 := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have hp : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
    push_cast
    rw [one_div]
    exact inv_anti₀ hp hs1
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp h2)

theorem h_sum_cube_split (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ) :
    ∑ a ∈ cube d N, F a = ∑ a ∈ inn d N i, F a + ∑ a ∈ face d N i, F a := by
  rw [← Finset.sum_filter_add_sum_filter_not (cube d N) (fun a => a i < N)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext a
  simp only [Finset.mem_filter, face, h_mem_cube]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, le_antisymm (h1 i) (not_lt.mp h2)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

theorem h_sum_shift (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ)
    (hF : ∀ a : Fin d →₀ ℕ, a i = 0 → F a = 0) :
    ∑ a ∈ cube d N, F a = ∑ b ∈ inn d N i, F (b + Finsupp.single i 1) := by
  rw [← Finset.sum_image (f := F) (g := fun b => b + Finsupp.single i 1)
    (fun x _ y _ h => add_right_cancel h)]
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [Finset.mem_image] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [h_mem_inn] at hb
    rw [h_mem_cube]
    intro j
    by_cases hj : j = i
    · subst hj; simp; have := hb.2; omega
    · simp [Finsupp.single_apply, Ne.symm hj]; exact hb.1 j
  · intro a ha hn
    apply hF
    by_contra h0
    apply hn
    simp only [Finset.mem_image]
    refine ⟨a - Finsupp.single i 1, ?_, h_sub_add_single h0⟩
    rw [h_mem_cube] at ha
    rw [h_mem_inn]
    refine ⟨fun j => le_trans (by simp) (ha j), ?_⟩
    have := ha i; simp; omega

theorem h_lterm_shift (i : Fin d) (b : Fin d →₀ ℕ) :
    lterm u amp i (b + Finsupp.single i 1) = (starRingEnd ℂ) (rterm u amp i b) := by
  unfold lterm rterm
  simp only [add_tsub_cancel_right, Finsupp.add_apply, Finsupp.single_eq_same, map_mul,
    Complex.conj_conj, Complex.conj_ofReal]
  push_cast
  ring

theorem h_sum_lterm (N : ℕ) (i : Fin d) :
    ∑ a ∈ cube d N, lterm u amp i a
      = (starRingEnd ℂ) (∑ a ∈ inn d N i, rterm u amp i a) := by
  rw [h_sum_shift d N i _ (fun a ha => by simp [lterm, ha]), map_sum]
  exact Finset.sum_congr rfl (fun b _ => h_lterm_shift i b)

theorem h_sum_range_of_disjoint {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (G : ℕ → Finset (Fin d →₀ ℕ)) (hd : ∀ M N : ℕ, M ≠ N → Disjoint (G M) (G N)) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2 ≤ B := by
  rw [← Finset.sum_biUnion (fun x _ y _ h => hd x y h)]
  exact hbes _

theorem h_faces_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ face d N i, ‖u a‖ ^ 2 ≤ B := by
  refine h_sum_range_of_disjoint hbes _ (fun M N h => ?_) M
  rw [Finset.disjoint_left]
  intro a h1 h2
  rw [h_mem_face] at h1 h2
  exact h (h1.2.symm.trans h2.2)

theorem h_shifted_faces_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ face d N i, ‖u (a + Finsupp.single i 1)‖ ^ 2 ≤ B := by
  have key : ∀ N, ∑ a ∈ face d N i, ‖u (a + Finsupp.single i 1)‖ ^ 2
      = ∑ a ∈ (face d N i).image (fun b => b + Finsupp.single i 1), ‖u a‖ ^ 2 := by
    intro N
    rw [Finset.sum_image (fun x _ y _ h => add_right_cancel h)]
  simp_rw [key]
  refine h_sum_range_of_disjoint hbes _ (fun M N h => ?_) M
  rw [Finset.disjoint_left]
  intro a h1 h2
  simp only [Finset.mem_image] at h1 h2
  obtain ⟨b, hb, rfl⟩ := h1
  obtain ⟨c, hc, hcb⟩ := h2
  rw [h_mem_face] at hb hc
  have := congrArg (fun f => f i) hcb
  simp at this
  exact h (by omega)

open BookProof.HermiteCarleman in
theorem solution {d N : ℕ} {a : Fin d →₀ ℕ} : a ∈ cube d N ↔ ∀ i, a i ≤ N := by
  exact h_mem_cube

