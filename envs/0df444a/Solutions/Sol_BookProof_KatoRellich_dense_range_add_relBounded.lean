-- Prove2me | solution 1 for BookProof.KatoRellich.dense_range_add_relBounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:38:09.077254+00:00
-- url     : https://prove2.me/submissions/f638121c-fea6-4126-925d-c072cc1ca1fd

-- Generated from ChapterKatoRellichRelative.lean — solution of BookProof.KatoRellich.dense_range_add_relBounded
import Mathlib
import Definitions.Def_ChapterKatoRellichRelative
import Theorems.Thm_BookProof_KatoRellich_norm_le_of_relBound
open BookProof.KatoRellich




open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution (H B : D →ₗ[ℂ] F) (hH : SymmetricOn D H) {a b e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : e ≠ 0)
    (hrel : ∀ x : D, ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖) (hq1 : a + b / |e| < 1)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F))) :
    Dense (Set.range fun x : D => (H x + B x) - ((e : ℂ) * Complex.I) • (x : F)) := by

  have he0 : (0 : ℝ) < |e| := abs_pos.mpr he
  set lam : ℂ := (e : ℂ) * Complex.I with hlam
  set q : ℝ := a + b / |e| with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hBq : ∀ x : D, ‖B x‖ ≤ q * ‖H x - lam • (x : F)‖ :=
    norm_le_of_relBound H B hH ha hb he hrel
  rw [Metric.dense_iff]
  intro y r hr
  obtain ⟨n, hn0⟩ : ∃ n : ℕ, q ^ n < (r / 2) / (‖y‖ + 1) :=
    exists_pow_lt_of_lt_one (by positivity) hq1
  have hn : q ^ n * ‖y‖ < r / 2 := by
    have h1 : q ^ n * ‖y‖ ≤ q ^ n * (‖y‖ + 1) := by
      have := pow_nonneg hq0 n
      nlinarith [norm_nonneg y]
    have h2 : q ^ n * (‖y‖ + 1) < ((r / 2) / (‖y‖ + 1)) * (‖y‖ + 1) := by
      have : (0 : ℝ) < ‖y‖ + 1 := by positivity
      exact mul_lt_mul_of_pos_right hn0 this
    have h3 : ((r / 2) / (‖y‖ + 1)) * (‖y‖ + 1) = r / 2 := by field_simp
    linarith
  set δ : ℝ := r / (4 * (n + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have step : ∀ v : F, ∃ x : D, ‖(H x - lam • (x : F)) - v‖ < δ := by
    intro v
    obtain ⟨z, hz1, x, hx⟩ := (Metric.dense_iff.mp hdense) v δ hδ
    have hx' : H x - lam • (x : F) = z := hx
    exact ⟨x, by rw [hx']; simpa [dist_eq_norm] using hz1⟩
  choose pick hpick using step
  set rr : ℕ → F := fun k => Nat.rec y (fun _ p => -(B (pick p))) k with hrrdef
  have hrr0 : rr 0 = y := rfl
  have hrrs : ∀ k, rr (k + 1) = -(B (pick (rr k))) := fun _ => rfl
  set v : ℕ → D := fun k => pick (rr k) with hvdef
  set S : ℕ → D := fun m => ∑ k ∈ Finset.range m, v k with hSdef
  have hrrbound : ∀ k, ‖rr k‖ ≤ q ^ k * ‖y‖ + k * δ := by
    intro k
    induction k with
    | zero => simp [hrr0]
    | succ k ih =>
      have h1 : ‖rr (k + 1)‖ ≤ q * ‖H (v k) - lam • (v k : F)‖ := by
        rw [hrrs k, norm_neg]
        exact hBq (v k)
      have hstep : ‖(H (v k) - lam • (v k : F)) - rr k‖ < δ := hpick (rr k)
      have h3 : ‖H (v k) - lam • (v k : F)‖ ≤ ‖rr k‖ + δ := by
        have heq : H (v k) - lam • (v k : F)
            = ((H (v k) - lam • (v k : F)) - rr k) + rr k := by abel
        rw [heq]
        calc ‖((H (v k) - lam • (v k : F)) - rr k) + rr k‖
            ≤ ‖(H (v k) - lam • (v k : F)) - rr k‖ + ‖rr k‖ := norm_add_le _ _
          _ ≤ δ + ‖rr k‖ := by linarith
          _ = ‖rr k‖ + δ := by ring
      have h4 : q * ‖H (v k) - lam • (v k : F)‖ ≤ q * (‖rr k‖ + δ) :=
        mul_le_mul_of_nonneg_left h3 hq0
      have h5 : q * (‖rr k‖ + δ) ≤ q * (q ^ k * ‖y‖ + k * δ + δ) := by nlinarith
      have h6 : q * (q ^ k * ‖y‖ + k * δ + δ) ≤ q ^ (k + 1) * ‖y‖ + (k + 1) * δ := by
        have hqk : 0 ≤ q ^ k := pow_nonneg hq0 k
        have hy : 0 ≤ ‖y‖ := norm_nonneg y
        have hkd : 0 ≤ (k : ℝ) * δ := by positivity
        have hmul : q * (q ^ k * ‖y‖) = q ^ (k + 1) * ‖y‖ := by ring
        nlinarith [hq1.le, hδ.le]
      push_cast
      push_cast at h5 h6
      linarith
  have hmain : ∀ m : ℕ,
      ‖(H (S m) + B (S m) - lam • (S m : F)) - (y - rr m)‖ ≤ m * δ := by
    intro m
    induction m with
    | zero => simp [hSdef, hrr0]
    | succ m ih =>
      have hSsucc : S (m + 1) = S m + v m := by
        simp [hSdef, Finset.sum_range_succ]
      have hdiff : (H (S (m + 1)) + B (S (m + 1)) - lam • ((S (m + 1) : D) : F))
            - (y - rr (m + 1))
          = ((H (S m) + B (S m) - lam • (S m : F)) - (y - rr m))
            + ((H (v m) - lam • (v m : F)) - rr m) := by
        simp only [hSsucc, hrrs m, map_add, Submodule.coe_add]
        module
      rw [hdiff]
      calc ‖((H (S m) + B (S m) - lam • (S m : F)) - (y - rr m))
              + ((H (v m) - lam • (v m : F)) - rr m)‖
          ≤ ‖(H (S m) + B (S m) - lam • (S m : F)) - (y - rr m)‖
            + ‖(H (v m) - lam • (v m : F)) - rr m‖ := norm_add_le _ _
        _ ≤ m * δ + δ := by
            have := hpick (rr m)
            simp only [hvdef]
            linarith [ih]
        _ = (m + 1 : ℕ) * δ := by push_cast; ring
  refine ⟨H (S n) + B (S n) - lam • (S n : F), ?_, ⟨S n, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hsplit : (H (S n) + B (S n) - lam • (S n : F)) - y
      = ((H (S n) + B (S n) - lam • (S n : F)) - (y - rr n)) - rr n := by abel
  have hfin : 2 * (n : ℝ) * δ ≤ r / 2 := by
    have heq : 2 * ((n : ℝ) + 1) * δ = r / 2 := by
      rw [hδdef]; field_simp; ring
    nlinarith [hδ.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  calc ‖(H (S n) + B (S n) - lam • (S n : F)) - y‖
      = ‖((H (S n) + B (S n) - lam • (S n : F)) - (y - rr n)) - rr n‖ := by rw [hsplit]
    _ ≤ ‖(H (S n) + B (S n) - lam • (S n : F)) - (y - rr n)‖ + ‖rr n‖ := norm_sub_le _ _
    _ ≤ n * δ + (q ^ n * ‖y‖ + n * δ) := add_le_add (hmain n) (hrrbound n)
    _ < r := by linarith
