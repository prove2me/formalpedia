-- Prove2me | solution 1 for BookProof.HermiteCarleman.ladder_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:35:36.326042+00:00
-- url     : https://prove2.me/submissions/faeb5bb5-fede-486a-b05c-08c410031cbf

-- Generated from ChapterHermiteCarlemanEsa.lean — theorem BookProof.HermiteCarleman.ladder_eq_zero
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

theorem sum_cube_split' (N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ) :
    ∑ a ∈ cube d N, F a = ∑ a ∈ inn d N i, F a + ∑ a ∈ face d N i, F a := by
  classical
  have h1 : face d N i = (cube d N).filter (fun a => ¬ a i < N) := by
    unfold face
    apply Finset.filter_congr
    intro a ha
    have := (mem_cube'.mp ha) i
    omega
  rw [h1, inn, Finset.sum_filter_add_sum_filter_not]

theorem flux_identity (hrec : LadderRec u lam amp z) (N : ℕ) :
    z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
      = ∑ i, (∑ a ∈ face d N i, rterm u amp i a).im := by
  have key : ∀ a, ((lam a : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ))
      + ∑ i, (rterm u amp i a + lterm u amp i a) = z * ((‖u a‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    have hn : ((‖u a‖ ^ 2 : ℝ) : ℂ) = starRingEnd ℂ (u a) * u a := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 := hrec a
    have e : ∑ i, (rterm u amp i a + lterm u amp i a) = starRingEnd ℂ (u a) *
        ∑ i, ((starRingEnd ℂ) (amp i) * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ)
                * u (a + Finsupp.single i 1)
            + amp i * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) * u (a - Finsupp.single i 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold rterm lterm; ring
    rw [e, hn]
    linear_combination (starRingEnd ℂ (u a)) * h2
  have T : ∑ a ∈ cube d N, ((lam a : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ))
      + ∑ i, (∑ a ∈ cube d N, rterm u amp i a + ∑ a ∈ cube d N, lterm u amp i a)
      = z * ((∑ a ∈ cube d N, ‖u a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum, ← Finset.sum_congr rfl (fun a _ => key a)]
    simp only [Finset.sum_add_distrib]
    congr 1
    congr 1 <;> exact Finset.sum_comm
  have T2 := congrArg Complex.im T
  have hsplit : ∀ i, ∑ a ∈ cube d N, rterm u amp i a
      = ∑ a ∈ inn d N i, rterm u amp i a + ∑ a ∈ face d N i, rterm u amp i a :=
    fun i => sum_cube_split' N i _
  simp only [sum_lterm, hsplit] at T2
  simp only [Complex.add_im, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, add_zero, Finset.sum_const_zero, zero_add,
    Complex.conj_im] at T2
  rw [← T2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.im_sum]; ring

theorem ladder_eq_zero {B : ℝ} (hz : z.im ≠ 0)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (hrec : LadderRec u lam amp z) : ∀ a, u a = 0 := by
  intro a0
  by_contra h0
  set c := ‖u a0‖ ^ 2 with hc
  have hcpos : 0 < c := by positivity
  set g : ℕ → ℝ := fun N => ∑ i, ‖amp i‖ * ((∑ a ∈ face d N i,
      (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i 1)‖ ^ 2)) / 2) with hg
  have hg0 : ∀ N, 0 ≤ g N := fun N =>
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _)
      (div_nonneg (Finset.sum_nonneg fun a _ => by positivity) (by norm_num))
  have hB0 : 0 ≤ B := by simpa using hbes ∅
  have hgs : Summable g := by
    refine summable_of_sum_range_le hg0 (c := (∑ i, ‖amp i‖) * B) fun M => ?_
    calc ∑ N ∈ Finset.range M, g N
        = ∑ i, ‖amp i‖ * ((∑ N ∈ Finset.range M, ∑ a ∈ face d N i, ‖u a‖ ^ 2
            + ∑ N ∈ Finset.range M, ∑ a ∈ face d N i, ‖u (a + Finsupp.single i 1)‖ ^ 2) / 2) := by
          rw [hg, Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, ← Finset.sum_div, ← Finset.sum_add_distrib]
          congr 2
          exact Finset.sum_congr rfl fun N _ => Finset.sum_add_distrib
      _ ≤ ∑ i, ‖amp i‖ * ((B + B) / 2) := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          have := faces_le hbes i M
          have := shifted_faces_le hbes i M
          linarith
      _ = (∑ i, ‖amp i‖) * B := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring
  have hflux : ∀ N, |z.im| * (∑ a ∈ cube d N, ‖u a‖ ^ 2) ≤ Real.sqrt ((N : ℝ) + 1) * g N := by
    intro N
    have hS : 0 ≤ ∑ a ∈ cube d N, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    calc |z.im| * (∑ a ∈ cube d N, ‖u a‖ ^ 2) = |z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2)| := by
          rw [abs_mul, abs_of_nonneg hS]
      _ = |∑ i, (∑ a ∈ face d N i, rterm u amp i a).im| := by rw [flux_identity hrec N]
      _ ≤ ∑ i, |(∑ a ∈ face d N i, rterm u amp i a).im| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, Real.sqrt ((N : ℝ) + 1) * (‖amp i‖ * ((∑ a ∈ face d N i,
          (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i 1)‖ ^ 2)) / 2)) :=
          Finset.sum_le_sum fun i _ => flux_bound N i
      _ = Real.sqrt ((N : ℝ) + 1) * g N := by rw [hg, Finset.mul_sum]
  set N0 := ∑ j, a0 j
  have hmem : ∀ N, a0 ∈ cube d (N + N0) := fun N => mem_cube'.mpr fun j => by
    have : a0 j ≤ N0 := Finset.single_le_sum (f := fun j => a0 j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
    omega
  have hzc : 0 < |z.im| * c := mul_pos (abs_pos.mpr hz) hcpos
  have hs2 : Summable (fun N : ℕ => (Real.sqrt (((N + N0 : ℕ) : ℝ) + 1))⁻¹) := by
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_)
      (((summable_nat_add_iff N0).mpr hgs).div_const (|z.im| * c))
    have hsq : 0 < Real.sqrt (((N + N0 : ℕ) : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h1 : c ≤ ∑ a ∈ cube d (N + N0), ‖u a‖ ^ 2 :=
      Finset.single_le_sum (f := fun a => ‖u a‖ ^ 2) (fun _ _ => by positivity) (hmem N)
    have h2 := hflux (N + N0)
    have h3 : |z.im| * c ≤ Real.sqrt (((N + N0 : ℕ) : ℝ) + 1) * g (N + N0) :=
      le_trans (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) h2
    rw [inv_eq_one_div, div_le_div_iff₀ hsq hzc]
    simpa [mul_comm] using h3
  exact not_summable_inv_sqrt ((summable_nat_add_iff N0).mp hs2)

end S79HC

theorem solution {B : ℝ} (hz : z.im ≠ 0)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (hrec : LadderRec u lam amp z) : ∀ a, u a = 0 := by
  apply S79HC.ladder_eq_zero <;> assumption
