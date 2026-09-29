-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_isSymmetricDom
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:26:37.201165+00:00
-- url     : https://prove2.me/submissions/f7b61697-1f3f-44cb-bd9a-fc7051be82d1

/- Adapted from Leonardo Pedro, timepiece commit 61595bc, Apache-2.0.
https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesLagrangianKatoRellich.lean -/
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterRitzCertificate
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
theorem inner_im_swap (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]

theorem inner_apply_self_im (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) (x : D) :
    (inner ℂ (T x) (x : F) : ℂ).im = 0 := by
  have h := congrArg Complex.im (hT x x)
  rw [inner_im_swap (T x) (x : F)] at h
  linarith

theorem norm_sub_smul_sq (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (d : ℝ) (x : D) :
    ‖H x - ((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = ‖H x‖ ^ 2 + d ^ 2 * ‖(x : F)‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  have h1 : (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ)
      = ((d : ℂ) * Complex.I) * inner ℂ (H x) (x : F) := inner_smul_right _ _ _
  have h2 : RCLike.re (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ) = 0 := by
    rw [h1]; simp [inner_apply_self_im H hH x]
  have h3 : ‖((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = d ^ 2 * ‖(x : F)‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow, sq_abs]
  rw [h2, h3]; ring

theorem dense_range_of_deficiencyTrivialAt [CompleteSpace F] (H : D →ₗ[ℂ] F) (w₀ : ℂ)
    (h : DeficiencyTrivialAt D H (starRingEnd ℂ w₀)) :
    Dense (Set.range fun x : D => H x - w₀ • (x : F)) := by
  set K : Submodule ℂ F := LinearMap.range (H - w₀ • D.subtype) with hK
  have hset : (K : Set F) = Set.range fun x : D => H x - w₀ • (x : F) := by
    ext u
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
    · rintro ⟨x, rfl⟩; exact ⟨x, by simp [LinearMap.sub_apply]⟩
  rw [← hset, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  refine h f fun v => ?_
  have hv := (Submodule.mem_orthogonal K f).mp hf (H v - w₀ • (v : F))
    ⟨v, by simp [LinearMap.sub_apply]⟩
  rw [inner_sub_left, inner_smul_left, sub_eq_zero] at hv
  exact hv

theorem exists_weak_graph_limit [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H)
    (d : ℝ) (hd : d ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)))
    (y : F) :
    ∃ u z : F, (∀ v : D, (inner ℂ (H v) u : ℂ) = inner ℂ (v : F) z) ∧
      z - ((d : ℂ) * Complex.I) • u = y ∧ (inner ℂ z u : ℂ).im = 0 := by
  have hdpos : 0 < |d| := abs_pos.mpr hd
  have hchoice : ∀ n : ℕ, ∃ x : D, ‖(H x - ((d : ℂ) * Complex.I) • (x : F)) - y‖ < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨p, hp1, x, hx⟩ := Metric.dense_iff.mp hdense y (1 / (n + 1)) hpos
    refine ⟨x, ?_⟩
    rw [← hx] at hp1
    simpa [dist_eq_norm] using hp1
  choose x hx using hchoice
  set Y : ℕ → F := fun n => H (x n) - ((d : ℂ) * Complex.I) • ((x n : F)) with hY
  have hYtend : Filter.Tendsto Y Filter.atTop (nhds y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hx n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hYcauchy : CauchySeq Y := hYtend.cauchySeq
  have hest : ∀ m n : ℕ, |d| * ‖(x m : F) - (x n : F)‖ ≤ ‖Y m - Y n‖ ∧
      ‖H (x m) - H (x n)‖ ≤ ‖Y m - Y n‖ := by
    intro m n
    have hsplit : Y m - Y n = H (x m - x n) - ((d : ℂ) * Complex.I) • ((x m - x n : D) : F) := by
      simp [hY, map_sub, smul_sub]
      abel
    have hsq := norm_sub_smul_sq H hH d (x m - x n)
    rw [← hsplit] at hsq
    have hcoe : ((x m - x n : D) : F) = (x m : F) - (x n : F) := rfl
    rw [hcoe, map_sub] at hsq
    constructor
    · nlinarith [norm_nonneg (Y m - Y n), norm_nonneg ((x m : F) - (x n : F)),
        norm_nonneg (H (x m) - H (x n)), sq_abs d, sq_nonneg (‖H (x m) - H (x n)‖)]
    · nlinarith [norm_nonneg (Y m - Y n), norm_nonneg ((x m : F) - (x n : F)),
        norm_nonneg (H (x m) - H (x n)), sq_nonneg d, sq_nonneg (d * ‖(x m : F) - (x n : F)‖)]
  have hxcauchy : CauchySeq (fun n => (x n : F)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hYcauchy (ε * |d|) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := (hest m n).1
    have h2 := hN m hm n hn
    rw [dist_eq_norm] at h2 ⊢
    nlinarith
  have hHxcauchy : CauchySeq (fun n => H (x n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hYcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := (hest m n).2
    have h2 := hN m hm n hn
    rw [dist_eq_norm] at h2 ⊢
    linarith
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hxcauchy
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hHxcauchy
  refine ⟨u, z, ?_, ?_, ?_⟩
  · intro v
    have h1 : Filter.Tendsto (fun n => (inner ℂ (H v) (x n : F) : ℂ)) Filter.atTop
        (nhds (inner ℂ (H v) u)) := Filter.Tendsto.inner tendsto_const_nhds hu
    have h2 : Filter.Tendsto (fun n => (inner ℂ (v : F) (H (x n)) : ℂ)) Filter.atTop
        (nhds (inner ℂ (v : F) z)) := Filter.Tendsto.inner tendsto_const_nhds hz
    have heq : ∀ n, (inner ℂ (H v) (x n : F) : ℂ) = inner ℂ (v : F) (H (x n)) := fun n => hH v (x n)
    exact tendsto_nhds_unique (by simpa [heq] using h1) h2
  · have hlim : Filter.Tendsto Y Filter.atTop (nhds (z - ((d : ℂ) * Complex.I) • u)) := by
      simpa [hY] using hz.sub (Filter.Tendsto.const_smul hu ((d : ℂ) * Complex.I))
    exact tendsto_nhds_unique hlim hYtend
  · have h1 : Filter.Tendsto (fun n => (inner ℂ (H (x n)) (x n : F) : ℂ)) Filter.atTop
        (nhds (inner ℂ z u)) := Filter.Tendsto.inner hz hu
    have h2 : Filter.Tendsto (fun n => (inner ℂ (H (x n)) (x n : F) : ℂ).im) Filter.atTop
        (nhds ((inner ℂ z u : ℂ).im)) := (Complex.continuous_im.tendsto _).comp h1
    have h3 : ∀ n, (inner ℂ (H (x n)) (x n : F) : ℂ).im = 0 :=
      fun n => inner_apply_self_im H hH (x n)
    simp only [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds

theorem deficiencyTrivialAt_of_dense_range [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (e : ℝ) (he : e ≠ 0) (σ : ℂ) (hσ : σ.im ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F)))
    (hdef : DeficiencyTrivialAt D H ((e : ℂ) * Complex.I)) :
    DeficiencyTrivialAt D H σ := by
  intro w hw
  obtain ⟨u, z, hu, hzy, him⟩ :=
    exists_weak_graph_limit H hH e he hdense ((σ - (e : ℂ) * Complex.I) • w)
  have hzeq : z = ((e : ℂ) * Complex.I) • u + (σ - (e : ℂ) * Complex.I) • w := by
    rw [← hzy]; abel
  have hs : ∀ v : D, (inner ℂ (H v) (w - u) : ℂ)
      = ((e : ℂ) * Complex.I) * inner ℂ (v : F) (w - u) := by
    intro v
    rw [inner_sub_right, inner_sub_right, hw v, hu v, hzeq, inner_add_right,
      inner_smul_right, inner_smul_right]
    ring
  have hwu : w = u := sub_eq_zero.mp (hdef (w - u) hs)
  have hzs : z = σ • w := by rw [hzeq, ← hwu]; module
  have hinner : (inner ℂ z u : ℂ) = starRingEnd ℂ σ * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [hzs, ← hwu, inner_smul_left, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [hinner, Complex.mul_im] at him
  simp only [Complex.ofReal_im, Complex.ofReal_re, Complex.conj_im, mul_zero, zero_add] at him
  have hnorm : ‖w‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact absurd (by linarith [neg_eq_zero.mp h] : σ.im = 0) hσ
    · exact h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg w])
end BookProof.FarisLavine
namespace BookProof.KatoRellich
open BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
theorem deficiencyTrivialAt_of_dense (T : D →ₗ[ℂ] F) (z : ℂ)
    (hd : Dense (Set.range fun x : D => T x - ((starRingEnd ℂ) z) • (x : F))) :
    DeficiencyTrivialAt D T z := by
  intro w hw
  have hclosed : IsClosed {y : F | (inner ℂ y w : ℂ) = 0} :=
    isClosed_eq (Continuous.inner continuous_id continuous_const) continuous_const
  have hsub : (Set.range fun x : D => T x - ((starRingEnd ℂ) z) • (x : F))
      ⊆ {y : F | (inner ℂ y w : ℂ) = 0} := by
    rintro _ ⟨x, rfl⟩
    simp only [Set.mem_setOf_eq, inner_sub_left, inner_smul_left, hw x, Complex.conj_conj]
    ring
  have huniv := hclosed.closure_subset_iff.mpr hsub
  rw [hd.closure_eq] at huniv
  exact inner_self_eq_zero.mp (huniv (Set.mem_univ w))

theorem symmetricOn_add {H B : D →ₗ[ℂ] F} (hH : SymmetricOn D H) (hB : SymmetricOn D B) :
    SymmetricOn D (H + B) := by
  intro x y
  simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hH x y, hB x y]

theorem norm_le_of_relBound (H B : D →ₗ[ℂ] F) (hH : SymmetricOn D H) {a b e : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : e ≠ 0)
    (hrel : ∀ x : D, ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖) (x : D) :
    ‖B x‖ ≤ (a + b / |e|) * ‖H x - ((e : ℂ) * Complex.I) • (x : F)‖ := by
  have he0 : (0 : ℝ) < |e| := abs_pos.mpr he
  set N : ℝ := ‖H x - ((e : ℂ) * Complex.I) • (x : F)‖ with hN
  have hsq : N ^ 2 = ‖H x‖ ^ 2 + e ^ 2 * ‖(x : F)‖ ^ 2 := norm_sub_smul_sq H hH e x
  have hN0 : 0 ≤ N := norm_nonneg _
  have h1 : ‖H x‖ ≤ N := by
    nlinarith [norm_nonneg (H x), sq_nonneg (e * ‖(x : F)‖), norm_nonneg (x : F),
      sq_nonneg ‖(x : F)‖]
  have h2 : |e| * ‖(x : F)‖ ≤ N := by
    nlinarith [norm_nonneg (H x), norm_nonneg (x : F), sq_abs e,
      mul_nonneg (abs_nonneg e) (norm_nonneg (x : F))]
  have h3 : b * ‖(x : F)‖ ≤ (b / |e|) * N := by
    rw [div_mul_eq_mul_div, le_div_iff₀ he0]
    nlinarith
  calc ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖ := hrel x
    _ ≤ a * N + (b / |e|) * N := by nlinarith
    _ = (a + b / |e|) * N := by ring

theorem dense_range_add_relBounded (H B : D →ₗ[ℂ] F) (hH : SymmetricOn D H) {a b e : ℝ}
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

theorem essentiallySelfAdjointOn_add_relBounded [CompleteSpace F] (H B : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (hB : SymmetricOn D B)
    {a b : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) (hb : 0 ≤ b)
    (hrel : ∀ x : D, ‖B x‖ ≤ a * ‖H x‖ + b * ‖(x : F)‖) :
    EssentiallySelfAdjointOn D (H + B) := by
  set K : D →ₗ[ℂ] F := H + B with hK
  have hKapply : ∀ x : D, K x = H x + B x := fun x => rfl
  have hKsymm : SymmetricOn D K := symmetricOn_add hH hB
  -- `H` has trivial deficiency spaces at every non-real point
  have hHall : ∀ σ : ℂ, σ.im ≠ 0 → DeficiencyTrivialAt D H σ := by
    intro σ hσ
    refine deficiencyTrivialAt_of_dense_range H hH 1 one_ne_zero σ hσ ?_ ?_
    · have := dense_range_of_deficiencyTrivialAt H ((1 : ℝ) * Complex.I) (by simpa using hesa.2)
      simpa using this
    · simpa using hesa.1
  -- a shift large enough to make the contraction factor `< 1`
  set e : ℝ := (b + 1) / (1 - a) with hedef
  have h1a : (0 : ℝ) < 1 - a := by linarith
  have he0' : (0 : ℝ) < e := by rw [hedef]; positivity
  have he0 : e ≠ 0 := ne_of_gt he0'
  have habse : |e| = e := abs_of_pos he0'
  have hqlt : ∀ d : ℝ, e ≤ |d| → a + b / |d| < 1 := by
    intro d hd
    have hd0 : (0 : ℝ) < |d| := lt_of_lt_of_le he0' hd
    have hbe : b / |d| ≤ b / e := by
      rcases eq_or_lt_of_le hb with h | h
      · simp [← h]
      · exact div_le_div_of_nonneg_left hb he0' hd
    have hlt : b / e < 1 - a := by
      rw [hedef, div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hdenseH : ∀ d : ℝ, d ≠ 0 →
      Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) := by
    intro d hd
    refine dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (hHall _ ?_)
    simp [hd]
  have hdenseK : ∀ d : ℝ, e ≤ |d| →
      Dense (Set.range fun x : D => (H x + B x) - ((d : ℂ) * Complex.I) • (x : F)) := by
    intro d hd
    have hd0 : d ≠ 0 := by
      intro h
      rw [h] at hd
      simp at hd
      linarith
    exact dense_range_add_relBounded H B hH ha hb hd0 hrel (hqlt d hd) (hdenseH d hd0)
  have hself : e ≤ |e| := le_of_eq habse.symm
  have hneg : e ≤ |(-e)| := by rw [abs_neg]; exact hself
  have hdefK : DeficiencyTrivialAt D K ((e : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_dense K _ ?_
    have hconj : (starRingEnd ℂ) ((e : ℂ) * Complex.I) = ((-e : ℝ) : ℂ) * Complex.I := by
      push_cast
      simp [mul_comm]
    rw [hconj]
    simpa [hKapply] using hdenseK (-e) hneg
  have hdenseKe : Dense (Set.range fun x : D => K x - ((e : ℂ) * Complex.I) • (x : F)) := by
    simpa [hKapply] using hdenseK e hself
  exact ⟨deficiencyTrivialAt_of_dense_range K hKsymm e he0 Complex.I (by simp) hdenseKe hdefK,
    deficiencyTrivialAt_of_dense_range K hKsymm e he0 (-Complex.I) (by simp) hdenseKe hdefK⟩
end BookProof.KatoRellich

namespace BookProof.FarisLavine
open BookProof.NavierStokesFlow
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
theorem essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn
    (D : Submodule ℂ F) (H : D →ₗ[ℂ] D) :
    EssentiallySelfAdjointOn D (D.subtype.comp H) ↔ HasZeroDeficiencyOn D H := by
  have key : ∀ (w : F) (z : ℂ),
      (∀ v : D, (inner ℂ ((D.subtype.comp H) v) w : ℂ) = z * inner ℂ (v : F) w) ↔
        ∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (z • w) := by
    intro w z
    constructor <;> intro h v
    · rw [inner_smul_right]; exact h v
    · have := h v; rwa [inner_smul_right] at this
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun w hw => h1 w ((key w Complex.I).2 hw), fun w hw => h2 w ((key w (-Complex.I)).2 ?_)⟩
    intro v
    rw [neg_smul]
    exact hw v
  · rintro ⟨h1, h2⟩
    refine ⟨fun w hw => h1 w ((key w Complex.I).1 hw), fun w hw => h2 w ?_⟩
    intro v
    rw [← neg_smul]
    exact (key w (-Complex.I)).1 hw v
end BookProof.FarisLavine

namespace BookProof.NavierStokesFlow.FullEsa
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
theorem IsSymmetricDom.add {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (hB : IsSymmetricDom B) :
    IsSymmetricDom (A + B) := by
  intro x y
  simp only [LinearMap.add_apply, Submodule.coe_add, inner_add_left, inner_add_right, hA x y,
    hB x y]

theorem IsSymmetricDom.sum {ι : Type*} (s : Finset ι) {A : ι → (D →ₗ[ℂ] D)}
    (hA : ∀ i ∈ s, IsSymmetricDom (A i)) : IsSymmetricDom (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (IsSymmetricDom.zero (D := D))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hA a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

theorem IsSymmetricDom.comp_of_commute {A B : D →ₗ[ℂ] D} (hA : IsSymmetricDom A)
    (hB : IsSymmetricDom B) (hcomm : A.comp B = B.comp A) : IsSymmetricDom (A.comp B) := by
  intro x y
  have h1 : (inner ℂ ((A (B x) : F)) (y : F) : ℂ) = inner ℂ ((B x : F)) ((A y : F)) := hA _ _
  have h2 : (inner ℂ ((B x : F)) ((A y : F)) : ℂ) = inner ℂ (x : F) ((B (A y) : F)) := hB _ _
  have h3 : B (A y) = A (B y) := by
    have := congrArg (fun T : D →ₗ[ℂ] D => T y) hcomm
    simpa using this.symm
  simpa [h3] using h1.trans h2
end BookProof.NavierStokesFlow.FullEsa

namespace BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.FullEsa
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
namespace LagrangianFullData
variable (L : LagrangianFullData F)
theorem hFull_decomposition :
    L.hFull = L.kinetic + L.viscous + L.drift + L.constraintOp := rfl

/- The square of a symmetric operator is symmetric. -/
theorem isSymmetricDom_sq {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) :
    IsSymmetricDom (A.comp A) :=
  hA.comp_of_commute hA rfl

theorem kinetic_isSymmetricDom : IsSymmetricDom L.kinetic :=
  IsSymmetricDom.real_smul
    (IsSymmetricDom.sum Finset.univ fun i _ => isSymmetricDom_sq (L.P_symm i)) _

theorem viscous_isSymmetricDom : IsSymmetricDom L.viscous :=
  IsSymmetricDom.real_smul
    (IsSymmetricDom.sum Finset.univ fun i _ => isSymmetricDom_sq (L.Q_symm i)) _

theorem drift_isSymmetricDom : IsSymmetricDom L.drift :=
  IsSymmetricDom.sum Finset.univ fun i _ => (L.drive_symm i).real_smul _

/- **The full transformed Navier–Stokes Hamiltonian is symmetric on its
domain**, unconditionally: each of the four terms is. -/
theorem hFull_isSymmetricDom : IsSymmetricDom L.hFull :=
  ((L.kinetic_isSymmetricDom.add L.viscous_isSymmetricDom).add
      L.drift_isSymmetricDom).add L.constraint_symm

/-! ### Positivity of the second-order part -/

/- The quadratic form of the square of a symmetric operator is the squared norm
of its value. -/
theorem inner_comp_self {D : Submodule ℂ F} {A : D →ₗ[ℂ] D} (hA : IsSymmetricDom A) (v : D) :
    (inner ℂ (v : F) ((A.comp A) v : F) : ℂ) = ((‖(A v : F)‖ ^ 2 : ℝ) : ℂ) := by
  have h := hA v (A v)
  simp only [LinearMap.comp_apply]
  rw [← h]
  simp

/- **The advection term of the transformed operator is positive**: its
quadratic form is `½∑‖Pᵢv‖²`.  This is the structural gain of the Lagrangian
change of variables — the Eulerian advection `−u_j∂_ju_i` becomes the positive
second-order Laplacian `−½Δ_X`. -/
theorem kinetic_inner (v : L.D) :
    (inner ℂ (v : F) (L.kinetic v : F) : ℂ)
      = (((1 / 2 : ℝ) * ∑ i : Fin 3, ‖(L.P i v : F)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [kinetic, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
    Submodule.coe_sum, inner_smul_right, inner_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => inner_comp_self (L.P_symm i) v

/- The viscous term is positive as well (`ν ≥ 0`). -/
theorem viscous_inner (v : L.D) :
    (inner ℂ (v : F) (L.viscous v : F) : ℂ)
      = ((L.nu * ∑ i : Fin 3, ‖(L.Q i v : F)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [viscous, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul,
    Submodule.coe_sum, inner_smul_right, inner_sum, Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => inner_comp_self (L.Q_symm i) v

theorem kinetic_nonneg (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re := by
  rw [L.kinetic_inner v, Complex.ofReal_re]
  have : (0 : ℝ) ≤ ∑ i : Fin 3, ‖(L.P i v : F)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

theorem viscous_nonneg (v : L.D) : 0 ≤ (inner ℂ (v : F) (L.viscous v : F) : ℂ).re := by
  rw [L.viscous_inner v, Complex.ofReal_re]
  have h : (0 : ℝ) ≤ ∑ i : Fin 3, ‖(L.Q i v : F)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  exact mul_nonneg L.nu_nonneg h


end LagrangianFullData
end BookProof.NavierStokesFlow.LagrangianEsa
open Filter Topology

namespace BookProof.NavierStokesFlow

namespace LagrangianKatoRellich

open FullEsa LagrangianEsa BookProof.FarisLavine BookProof.KatoRellich
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin

/-! ## The split into second-order and low-order parts -/

section Abstract

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

/- The **positive second-order part** `T = ½∑Pᵢ² + ν∑Qᵢ²` of the transformed
Hamiltonian: advection plus viscosity. -/
/- The low-order remainder `∑fᵢDᵢ + C`: the first-order drift plus the
zeroth-order volume-preservation constraint. -/
/- The transformed (Lagrangian) Navier–Stokes Hamiltonian, viewed as an
operator into the ambient space — the form the closure and shift-invert
machinery works with. -/
theorem hFull_eq_add : L.hFull = secondOrder L + lowOrder L := by
  simp only [LagrangianFullData.hFull, secondOrder, lowOrder]
  abel

theorem secondOrder_isSymmetricDom : IsSymmetricDom (secondOrder L) :=
  L.kinetic_isSymmetricDom.add L.viscous_isSymmetricDom

theorem lowOrder_isSymmetricDom : IsSymmetricDom (lowOrder L) :=
  L.drift_isSymmetricDom.add L.constraint_symm

theorem lagrangianCore_symmetricOn : SymmetricOn L.D (lagrangianCore L) :=
  fun x y => L.hFull_isSymmetricDom x y

/- The quadratic form of the second-order part is the sum of the two positive
quadratic forms. -/
theorem secondOrder_inner (v : L.D) :
    (inner ℂ (v : F) (secondOrder L v : F) : ℂ).re
      = (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re
        + (inner ℂ (v : F) (L.viscous v : F) : ℂ).re := by
  simp only [secondOrder, LinearMap.add_apply, Submodule.coe_add, inner_add_right,
    Complex.add_re]

/-! ### The interpolation inequality -/

/- **The interpolation inequality, squared form.**  Each parcel momentum obeys
`‖Pᵢ v‖² ≤ 2‖v‖‖T v‖`: the square of the first-order operator is dominated by
the *quadratic form* of the positive second-order part, because every other
term of that form is nonnegative. -/
theorem norm_P_sq_le (v : L.D) (i : Fin 3) :
    ‖(L.P i v : F)‖ ^ 2 ≤ 2 * (‖(v : F)‖ * ‖(secondOrder L v : F)‖) := by
  have hk : (inner ℂ (v : F) (L.kinetic v : F) : ℂ).re
      = (1 / 2 : ℝ) * ∑ j : Fin 3, ‖(L.P j v : F)‖ ^ 2 := by
    rw [L.kinetic_inner v, Complex.ofReal_re]
  have hsingle : ‖(L.P i v : F)‖ ^ 2 ≤ ∑ j : Fin 3, ‖(L.P j v : F)‖ ^ 2 :=
    Finset.single_le_sum (f := fun j : Fin 3 => ‖(L.P j v : F)‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hv : 0 ≤ (inner ℂ (v : F) (L.viscous v : F) : ℂ).re := L.viscous_nonneg v
  have hform : (1 / 2 : ℝ) * ‖(L.P i v : F)‖ ^ 2
      ≤ (inner ℂ (v : F) (secondOrder L v : F) : ℂ).re := by
    rw [secondOrder_inner L v, hk]
    nlinarith
  have hcs : (inner ℂ (v : F) (secondOrder L v : F) : ℂ).re
      ≤ ‖(v : F)‖ * ‖(secondOrder L v : F)‖ := by
    calc (inner ℂ (v : F) (secondOrder L v : F) : ℂ).re
        ≤ ‖(inner ℂ (v : F) (secondOrder L v : F) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖(v : F)‖ * ‖(secondOrder L v : F)‖ := norm_inner_le_norm _ _
  linarith

/- **The interpolation inequality.**  For every `ε > 0` the parcel momentum is
bounded by `ε` times the second-order part plus a multiple of the identity: the
first-order operators of the Lagrangian picture have *arbitrarily small*
relative bound with respect to the positive second-order part. -/
theorem norm_P_le (v : L.D) (i : Fin 3) {eps : ℝ} (heps : 0 < eps) :
    ‖(L.P i v : F)‖ ≤ eps * ‖(secondOrder L v : F)‖ + (1 / (2 * eps)) * ‖(v : F)‖ := by
  set A : ℝ := ‖(v : F)‖ with hA
  set B : ℝ := ‖(secondOrder L v : F)‖ with hB
  set x : ℝ := ‖(L.P i v : F)‖ with hx
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hx0 : 0 ≤ x := norm_nonneg _
  have hsq : x ^ 2 ≤ 2 * (A * B) := norm_P_sq_le L v i
  have hR0 : 0 ≤ eps * B + (1 / (2 * eps)) * A := by positivity
  have hamgm : 2 * (A * B) ≤ (eps * B + (1 / (2 * eps)) * A) ^ 2 := by
    have h := sq_nonneg (eps * B - (1 / (2 * eps)) * A)
    have he : eps * (1 / (2 * eps)) = 1 / 2 := by field_simp
    nlinarith [h, he]
  nlinarith [hsq, hamgm, hR0, hx0]

/- The interpolation inequality summed over the three components. -/
theorem norm_sum_P_le (v : L.D) {eps : ℝ} (heps : 0 < eps) :
    ∑ j : Fin 3, ‖(L.P j v : F)‖
      ≤ 3 * (eps * ‖(secondOrder L v : F)‖ + (1 / (2 * eps)) * ‖(v : F)‖) := by
  calc ∑ j : Fin 3, ‖(L.P j v : F)‖
      ≤ ∑ _j : Fin 3, (eps * ‖(secondOrder L v : F)‖ + (1 / (2 * eps)) * ‖(v : F)‖) :=
        Finset.sum_le_sum fun j _ => norm_P_le L v j heps
    _ = 3 * (eps * ‖(secondOrder L v : F)‖ + (1 / (2 * eps)) * ‖(v : F)‖) := by
        simp [Finset.sum_const]
        ring

/-! ### The relative bound for the low-order part -/

/- **The low-order part is relatively bounded with any prescribed relative
bound.**  If the first-order drift is dominated by the parcel momenta and the
constraint term is bounded, then for every `a > 0` there is `b ≥ 0` with
`‖(∑fᵢDᵢ + C)v‖ ≤ a‖T v‖ + b‖v‖`. -/
theorem lowOrder_relBound {kap kap' cc : ℝ} (hkap : 0 ≤ kap) (hkap' : 0 ≤ kap') (hcc : 0 ≤ cc)
    (hdrift : ∀ v : L.D,
      ‖(L.drift v : F)‖ ≤ kap * (∑ j : Fin 3, ‖(L.P j v : F)‖) + kap' * ‖(v : F)‖)
    (hC : ∀ v : L.D, ‖(L.constraintOp v : F)‖ ≤ cc * ‖(v : F)‖) {a : ℝ} (ha : 0 < a) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ v : L.D,
      ‖(lowOrder L v : F)‖ ≤ a * ‖(secondOrder L v : F)‖ + b * ‖(v : F)‖ := by
  set K : ℝ := 3 * kap with hK
  have hK0 : 0 ≤ K := by positivity
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  set eps : ℝ := a / (K + 1) with heps
  have heps0 : 0 < eps := div_pos ha hK1
  have hKeps : K * eps ≤ a := by
    rw [heps, mul_div_assoc', div_le_iff₀ hK1]
    nlinarith
  refine ⟨K * (1 / (2 * eps)) + kap' + cc, by positivity, fun v => ?_⟩
  have hA0 : 0 ≤ ‖(v : F)‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖(secondOrder L v : F)‖ := norm_nonneg _
  have hsum : kap * (∑ j : Fin 3, ‖(L.P j v : F)‖)
      ≤ K * (eps * ‖(secondOrder L v : F)‖ + (1 / (2 * eps)) * ‖(v : F)‖) := by
    have := mul_le_mul_of_nonneg_left (norm_sum_P_le L v heps0) hkap
    rw [hK]
    nlinarith
  have hlow : (lowOrder L v : F) = (L.drift v : F) + (L.constraintOp v : F) := by
    simp [lowOrder]
  calc ‖(lowOrder L v : F)‖ ≤ ‖(L.drift v : F)‖ + ‖(L.constraintOp v : F)‖ := by
        rw [hlow]; exact norm_add_le _ _
    _ ≤ (kap * (∑ j : Fin 3, ‖(L.P j v : F)‖) + kap' * ‖(v : F)‖) + cc * ‖(v : F)‖ :=
        add_le_add (hdrift v) (hC v)
    _ ≤ K * (eps * ‖(secondOrder L v : F)‖ + (1 / (2 * eps)) * ‖(v : F)‖)
        + kap' * ‖(v : F)‖ + cc * ‖(v : F)‖ := by linarith
    _ ≤ a * ‖(secondOrder L v : F)‖
        + (K * (1 / (2 * eps)) + kap' + cc) * ‖(v : F)‖ := by nlinarith

/-! ### The Kato–Rellich theorem for the transformed Hamiltonian -/

/- **The headline: Kato–Rellich for the transformed Navier–Stokes
Hamiltonian.**  If the *positive second-order part* `T = ½∑Pᵢ² + ν∑Qᵢ²` is
essentially self-adjoint on the domain, the first-order drift is dominated by
the parcel momenta and the constraint term is bounded, then the **full**
transformed Hamiltonian `ĥ_full = T + ∑fᵢDᵢ + C` is essentially self-adjoint on
the same domain.  The drift is allowed to be unbounded; only its domination by
`T` — a consequence of the positivity gained by the Lagrangian change of
variables — is used. -/
theorem hFull_essentiallySelfAdjointOn [CompleteSpace F] {kap kap' cc : ℝ}
    (hkap : 0 ≤ kap) (hkap' : 0 ≤ kap') (hcc : 0 ≤ cc)
    (hdrift : ∀ v : L.D,
      ‖(L.drift v : F)‖ ≤ kap * (∑ j : Fin 3, ‖(L.P j v : F)‖) + kap' * ‖(v : F)‖)
    (hC : ∀ v : L.D, ‖(L.constraintOp v : F)‖ ≤ cc * ‖(v : F)‖)
    (hT : EssentiallySelfAdjointOn L.D (L.D.subtype.comp (secondOrder L))) :
    EssentiallySelfAdjointOn L.D (lagrangianCore L) := by
  obtain ⟨b, hb0, hb⟩ := lowOrder_relBound L hkap hkap' hcc hdrift hC (a := 1 / 2) (by norm_num)
  have hsplit : lagrangianCore L
      = L.D.subtype.comp (secondOrder L) + L.D.subtype.comp (lowOrder L) := by
    rw [lagrangianCore, hFull_eq_add L]
    ext x
    simp
  rw [hsplit]
  refine essentiallySelfAdjointOn_add_relBounded _ _
    (fun x y => secondOrder_isSymmetricDom L x y) hT
    (fun x y => lowOrder_isSymmetricDom L x y) (a := 1 / 2) (b := b)
    (by norm_num) (by norm_num) hb0 ?_
  intro x
  simpa using hb x

/- The same statement in the `HasZeroDeficiencyOn` form used throughout the
Navier–Stokes chapters. -/
theorem hFull_hasZeroDeficiencyOn [CompleteSpace F] {kap kap' cc : ℝ}
    (hkap : 0 ≤ kap) (hkap' : 0 ≤ kap') (hcc : 0 ≤ cc)
    (hdrift : ∀ v : L.D,
      ‖(L.drift v : F)‖ ≤ kap * (∑ j : Fin 3, ‖(L.P j v : F)‖) + kap' * ‖(v : F)‖)
    (hC : ∀ v : L.D, ‖(L.constraintOp v : F)‖ ≤ cc * ‖(v : F)‖)
    (hT : HasZeroDeficiencyOn L.D (secondOrder L)) :
    HasZeroDeficiencyOn L.D L.hFull :=
  (essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn L.D L.hFull).mp
    (hFull_essentiallySelfAdjointOn L hkap hkap' hcc hdrift hC
      ((essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn L.D (secondOrder L)).mpr hT))

/-! ### The physical case: the drift generators are the parcel momenta -/

/- In the Lagrangian picture the first-order term is `f·∇_X`, i.e. the drift
generators *are* the parcel momenta.  Then the domination hypothesis holds
automatically, with `κ = ∑ᵢ|fᵢ|`. -/
theorem drift_dominated_of_drive_eq_P (hdrive : L.drive = L.P) (v : L.D) :
    ‖(L.drift v : F)‖
      ≤ (∑ i : Fin 3, |L.force i|) * (∑ j : Fin 3, ‖(L.P j v : F)‖) + 0 * ‖(v : F)‖ := by
  have hdriftsum : (L.drift v : F) = ∑ i : Fin 3, ((L.force i : ℝ) : ℂ) • (L.P i v : F) := by
    simp only [LagrangianFullData.drift, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sum, Submodule.coe_smul, hdrive]
  have hterms : ‖(L.drift v : F)‖ ≤ ∑ i : Fin 3, |L.force i| * ‖(L.P i v : F)‖ := by
    rw [hdriftsum]
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_smul]
    simp
  have hle : ∀ i : Fin 3, |L.force i| * ‖(L.P i v : F)‖
      ≤ |L.force i| * (∑ j : Fin 3, ‖(L.P j v : F)‖) := by
    intro i
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact Finset.single_le_sum (f := fun j : Fin 3 => ‖(L.P j v : F)‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  calc ‖(L.drift v : F)‖ ≤ ∑ i : Fin 3, |L.force i| * ‖(L.P i v : F)‖ := hterms
    _ ≤ ∑ i : Fin 3, |L.force i| * (∑ j : Fin 3, ‖(L.P j v : F)‖) :=
        Finset.sum_le_sum fun i _ => hle i
    _ = (∑ i : Fin 3, |L.force i|) * (∑ j : Fin 3, ‖(L.P j v : F)‖) := by
        rw [Finset.sum_mul]
    _ = (∑ i : Fin 3, |L.force i|) * (∑ j : Fin 3, ‖(L.P j v : F)‖) + 0 * ‖(v : F)‖ := by ring

/- **Kato–Rellich in the physical Lagrangian case.**  With `Dᵢ = Pᵢ` and a
bounded constraint, essential self-adjointness of the positive second-order part
alone gives it for the full transformed Hamiltonian. -/
theorem hFull_essentiallySelfAdjointOn_of_drive_eq_P [CompleteSpace F] (hdrive : L.drive = L.P)
    {cc : ℝ} (hcc : 0 ≤ cc) (hC : ∀ v : L.D, ‖(L.constraintOp v : F)‖ ≤ cc * ‖(v : F)‖)
    (hT : EssentiallySelfAdjointOn L.D (L.D.subtype.comp (secondOrder L))) :
    EssentiallySelfAdjointOn L.D (lagrangianCore L) :=
  hFull_essentiallySelfAdjointOn L
    (Finset.sum_nonneg fun _ _ => abs_nonneg _) le_rfl hcc
    (drift_dominated_of_drive_eq_P L hdrive) hC hT

theorem hFull_hasZeroDeficiencyOn_of_drive_eq_P [CompleteSpace F] (hdrive : L.drive = L.P)
    {cc : ℝ} (hcc : 0 ≤ cc) (hC : ∀ v : L.D, ‖(L.constraintOp v : F)‖ ≤ cc * ‖(v : F)‖)
    (hT : HasZeroDeficiencyOn L.D (secondOrder L)) :
    HasZeroDeficiencyOn L.D L.hFull :=
  hFull_hasZeroDeficiencyOn L (Finset.sum_nonneg fun _ _ => abs_nonneg _) le_rfl hcc
    (drift_dominated_of_drive_eq_P L hdrive) hC hT


end Abstract
end LagrangianKatoRellich
end BookProof.NavierStokesFlow
-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — theorem BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_isSymmetricDom
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich
















open Filter Topology



open FullEsa LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
theorem solution : IsSymmetricDom (lowOrder L) := by
  exact BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_isSymmetricDom L
#print axioms solution
