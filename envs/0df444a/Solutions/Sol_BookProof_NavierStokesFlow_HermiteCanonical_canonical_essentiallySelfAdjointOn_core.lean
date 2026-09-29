-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteCanonical.canonical_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:15:20.679251+00:00
-- url     : https://prove2.me/submissions/3c878177-8c7e-4077-a9c4-257d0a3179d5

import Definitions.Def_ChapterNavierStokesHermiteCanonical
import Definitions.Def_ChapterNavierStokesSignedShift
namespace BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
theorem inner_im_swap (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]

theorem inner_apply_self_im (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) (x : D) :
    (inner ℂ (T x) (x : F) : ℂ).im = 0 := by
  have h := congrArg Complex.im (hT x x)
  rw [inner_im_swap (T x) (x : F)] at h
  linarith

theorem quadForm_im (N : D →ₗ[ℂ] F) (hN : SymmetricOn D N) (x : D) :
    (inner ℂ (x : F) (N x) : ℂ).im = 0 := by
  rw [inner_im_swap (N x) (x : F), inner_apply_self_im N hN x, neg_zero]

theorem commForm_eq (H N : D →ₗ[ℂ] F) (x : D) :
    commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im := by
  rw [commForm, Complex.mul_re]
  simp [Complex.sub_im, inner_im_swap (H x) (N x)]
  ring

theorem deficiencyTrivialAt_of_farisLavine
    (H N : D →ₗ[ℂ] F) (c d : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hd : c < 2 * |d|) :
    DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) := by
  intro w hw
  obtain ⟨g, hg⟩ := hNsurj w
  have key := hw g
  rw [← hg, inner_add_right, inner_add_right] at key
  have him := congrArg Complex.im key
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re] at him
  have hBim : (inner ℂ (H g) (g : F) : ℂ).im = 0 := inner_apply_self_im H hH g
  have hPim : (inner ℂ (g : F) (N g) : ℂ).im = 0 := quadForm_im N hN g
  have hQim : (inner ℂ (g : F) (g : F) : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) (g : F)
  have hQre : (inner ℂ (g : F) (g : F) : ℂ).re = ‖(g : F)‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (g : F)
  set t : ℝ := quadForm N g + ‖(g : F)‖ ^ 2 with ht
  have hAim : (inner ℂ (H g) (N g) : ℂ).im = d * t := by
    rw [hBim, hPim, hQim, hQre] at him
    simp only [quadForm, ht]
    linarith [him]
  have htnn : 0 ≤ t := by have := hNpos g; positivity
  have habs : |commForm H N g| = 2 * |d| * t := by
    rw [commForm_eq, hAim, abs_mul, abs_mul, abs_of_nonneg htnn]
    norm_num
    ring
  have h1 : 2 * |d| * t ≤ c * quadForm N g := habs ▸ hcomm g
  have h2 : c * quadForm N g ≤ c * t := by
    have hle : quadForm N g ≤ t := by rw [ht]; nlinarith [sq_nonneg ‖(g : F)‖]
    exact mul_le_mul_of_nonneg_left hle hc
  have ht0 : t = 0 := by nlinarith
  have hgz : (g : F) = 0 := by
    have hnn := hNpos g
    have h4 : ‖(g : F)‖ ^ 2 = 0 := by rw [ht] at ht0; nlinarith [sq_nonneg ‖(g : F)‖]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (g : F)])
  have hg0 : g = 0 := Subtype.ext hgz
  rw [← hg, hg0]
  simp

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

theorem essentiallySelfAdjointOn_of_farisLavine [CompleteSpace F]
    (H N : D →ₗ[ℂ] F) (c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x) :
    EssentiallySelfAdjointOn D H := by
  set d : ℝ := c + 1 with hdd
  have hdpos : 0 < d := by simp [hdd]; linarith
  have hdabs : |d| = d := abs_of_pos hdpos
  have hd0 : d ≠ 0 := ne_of_gt hdpos
  have hdgt : c < 2 * |d| := by rw [hdabs, hdd]; linarith
  have hplus : DeficiencyTrivialAt D H ((d : ℂ) * Complex.I) :=
    deficiencyTrivialAt_of_farisLavine H N c d hH hN hc hNpos hNsurj hcomm hdgt
  have hminus : DeficiencyTrivialAt D H (((-d : ℝ) : ℂ) * Complex.I) := by
    refine deficiencyTrivialAt_of_farisLavine H N c (-d) hH hN hc hNpos hNsurj hcomm ?_
    rwa [abs_neg]
  have hconj : starRingEnd ℂ ((d : ℂ) * Complex.I) = ((-d : ℝ) : ℂ) * Complex.I := by
    simp
  have hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) :=
    dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (by rw [hconj]; exact hminus)
  exact ⟨deficiencyTrivialAt_of_dense_range H hH d hd0 Complex.I (by simp) hdense hplus,
    deficiencyTrivialAt_of_dense_range H hH d hd0 (-Complex.I) (by simp) hdense hplus⟩

theorem essentiallySelfAdjointOn_top_of_symmetric [CompleteSpace F]
    (H : (⊤ : Submodule ℂ F) →ₗ[ℂ] F) (hH : SymmetricOn ⊤ H) :
    EssentiallySelfAdjointOn (⊤ : Submodule ℂ F) H := by
  refine essentiallySelfAdjointOn_of_farisLavine H (⊤ : Submodule ℂ F).subtype 0 hH
    (fun x y => rfl) le_rfl (fun x => ?_)
    (fun f => ⟨⟨(2 : ℂ)⁻¹ • f, trivial⟩, ?_⟩) (fun x => ?_)
  · have hq : quadForm (⊤ : Submodule ℂ F).subtype x = ‖(x : F)‖ ^ 2 := by
      simp only [quadForm, Submodule.subtype_apply]
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x : F)
    rw [hq]; positivity
  · change (2 : ℂ)⁻¹ • f + (2 : ℂ)⁻¹ • f = f
    rw [← add_smul]
    norm_num
  · have h : (inner ℂ (H x) ((⊤ : Submodule ℂ F).subtype x) : ℂ).im = 0 :=
      inner_apply_self_im H hH x
    rw [commForm_eq, h]
    simp

theorem essentiallySelfAdjointOn_restrict_of_graph_core
    {C : Submodule ℂ F} (hCD : C ≤ D) (H : D →ₗ[ℂ] F)
    (hcore : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ y : D, (y : F) ∈ C ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖H y - H x‖ < ε)
    (hdef : EssentiallySelfAdjointOn D H) :
    EssentiallySelfAdjointOn C (H.comp (Submodule.inclusion hCD)) := by
  have main : ∀ σ : ℂ, DeficiencyTrivialAt D H σ →
      DeficiencyTrivialAt C (H.comp (Submodule.inclusion hCD)) σ := by
    intro σ hσ w hw
    refine hσ w fun x => ?_
    have hzero : ∀ ε : ℝ, 0 < ε →
        ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖ ≤ ε * (1 + ‖σ‖) * ‖w‖ := by
      intro ε hε
      obtain ⟨y, hyC, hy1, hy2⟩ := hcore x ε hε
      have hwy := hw ⟨(y : F), hyC⟩
      have hHy : (H.comp (Submodule.inclusion hCD)) ⟨(y : F), hyC⟩ = H y := by
        simp only [LinearMap.comp_apply]
        congr 1
      rw [hHy] at hwy
      have hsplit : (inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w
          = (inner ℂ (H x - H y) w : ℂ) + σ * inner ℂ ((y : F) - (x : F)) w := by
        rw [inner_sub_left, inner_sub_left, hwy]
        push_cast
        ring
      calc ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖
          ≤ ‖(inner ℂ (H x - H y) w : ℂ)‖ + ‖σ * (inner ℂ ((y : F) - (x : F)) w : ℂ)‖ := by
            rw [hsplit]; exact norm_add_le _ _
        _ ≤ ‖H x - H y‖ * ‖w‖ + ‖σ‖ * (‖(y : F) - (x : F)‖ * ‖w‖) := by
            gcongr
            · exact norm_inner_le_norm _ _
            · rw [norm_mul]
              gcongr
              exact norm_inner_le_norm _ _
        _ ≤ ε * (1 + ‖σ‖) * ‖w‖ := by
            have h1 : ‖H x - H y‖ ≤ ε := by
              rw [← norm_neg]; simpa [neg_sub] using hy2.le
            have h2 : ‖(y : F) - (x : F)‖ ≤ ε := hy1.le
            have hA : ‖H x - H y‖ * ‖w‖ ≤ ε * ‖w‖ :=
              mul_le_mul_of_nonneg_right h1 (norm_nonneg w)
            have hB : ‖σ‖ * (‖(y : F) - (x : F)‖ * ‖w‖) ≤ ‖σ‖ * (ε * ‖w‖) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (norm_nonneg w))
                (norm_nonneg σ)
            have hsum : ε * ‖w‖ + ‖σ‖ * (ε * ‖w‖) = ε * (1 + ‖σ‖) * ‖w‖ := by ring
            linarith
    have hnn : ‖(inner ℂ (H x) w : ℂ) - σ * inner ℂ (x : F) w‖ ≤ 0 := by
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hpos : 0 < δ / ((1 + ‖σ‖) * (1 + ‖w‖)) := by positivity
      have := hzero _ hpos
      have hbound : δ / ((1 + ‖σ‖) * (1 + ‖w‖)) * (1 + ‖σ‖) * ‖w‖ ≤ δ := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [norm_nonneg w, norm_nonneg σ, hδ.le]
      linarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hnn)
  exact ⟨main _ hdef.1, main _ hdef.2⟩

theorem essentiallySelfAdjointOn_core_of_farisLavine [CompleteSpace F]
    {C : Submodule ℂ F} (hCD : C ≤ D) (H N : D →ₗ[ℂ] F) (a b c : ℝ)
    (hH : SymmetricOn D H) (hN : SymmetricOn D N)
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm N x)
    (hNsurj : ∀ f : F, ∃ x : D, N x + (x : F) = f)
    (hcomm : ∀ x : D, |commForm H N x| ≤ c * quadForm N x)
    (hrel : ∀ x : D, ‖H x‖ ^ 2 ≤ a * ‖N x‖ ^ 2 + b * ‖(x : F)‖ ^ 2)
    (hNcore : ∀ (x : D) (ε : ℝ), 0 < ε → ∃ y : D, (y : F) ∈ C ∧
      ‖(y : F) - (x : F)‖ < ε ∧ ‖N y - N x‖ < ε) :
    EssentiallySelfAdjointOn C (H.comp (Submodule.inclusion hCD)) := by
  refine essentiallySelfAdjointOn_restrict_of_graph_core hCD H (fun x ε hε => ?_)
    (essentiallySelfAdjointOn_of_farisLavine H N c hH hN hc hNpos hNsurj hcomm)
  set K : ℝ := |a| + |b| + 1 with hK
  have hKpos : 0 < K := by positivity
  set δ : ℝ := min ε (ε / Real.sqrt K) with hδ
  have hδpos : 0 < δ := by
    refine lt_min hε ?_
    positivity
  obtain ⟨y, hyC, hy1, hy2⟩ := hNcore x δ hδpos
  refine ⟨y, hyC, lt_of_lt_of_le hy1 (min_le_left _ _), ?_⟩
  have hdiff : H y - H x = H (y - x) := by rw [map_sub]
  have hNdiff : N y - N x = N (y - x) := by rw [map_sub]
  have hcoe : ((y - x : D) : F) = (y : F) - (x : F) := rfl
  have hsq := hrel (y - x)
  rw [← hdiff, ← hNdiff, hcoe] at hsq
  have hb1 : ‖N y - N x‖ ≤ δ := hy2.le
  have hb2 : ‖(y : F) - (x : F)‖ ≤ δ := hy1.le
  have hδK : δ ^ 2 * K ≤ ε ^ 2 := by
    have h1 : δ ≤ ε / Real.sqrt K := min_le_right _ _
    have hsqrt : Real.sqrt K ^ 2 = K := Real.sq_sqrt hKpos.le
    have hsqrtpos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hKpos
    have h2 : δ * Real.sqrt K ≤ ε := by
      rw [le_div_iff₀ hsqrtpos] at h1
      exact h1
    have h3 : (δ * Real.sqrt K) ^ 2 ≤ ε ^ 2 := by
      nlinarith [mul_nonneg hδpos.le hsqrtpos.le]
    calc δ ^ 2 * K = (δ * Real.sqrt K) ^ 2 := by rw [mul_pow, hsqrt]
      _ ≤ ε ^ 2 := h3
  have hfinal : ‖H y - H x‖ ^ 2 < ε ^ 2 := by
    have hnn1 : 0 ≤ ‖N y - N x‖ := norm_nonneg _
    have hnn2 : 0 ≤ ‖(y : F) - (x : F)‖ := norm_nonneg _
    have hle : a * ‖N y - N x‖ ^ 2 + b * ‖(y : F) - (x : F)‖ ^ 2 ≤ (|a| + |b|) * δ ^ 2 := by
      have hs1 : ‖N y - N x‖ ^ 2 ≤ δ ^ 2 := by nlinarith
      have hs2 : ‖(y : F) - (x : F)‖ ^ 2 ≤ δ ^ 2 := by nlinarith
      have ha : a * ‖N y - N x‖ ^ 2 ≤ |a| * δ ^ 2 :=
        le_trans (by nlinarith [le_abs_self a, sq_nonneg ‖N y - N x‖])
          (mul_le_mul_of_nonneg_left hs1 (abs_nonneg a))
      have hbb : b * ‖(y : F) - (x : F)‖ ^ 2 ≤ |b| * δ ^ 2 :=
        le_trans (by nlinarith [le_abs_self b, sq_nonneg ‖(y : F) - (x : F)‖])
          (mul_le_mul_of_nonneg_left hs2 (abs_nonneg b))
      linarith
    have hstrict : (|a| + |b|) * δ ^ 2 < ε ^ 2 := by
      have : δ ^ 2 * K = (|a| + |b|) * δ ^ 2 + δ ^ 2 := by rw [hK]; ring
      nlinarith [pow_pos hδpos 2]
    linarith
  have hεpos : (0 : ℝ) < ε := hε
  nlinarith [norm_nonneg (H y - H x)]

end BookProof.FarisLavine
open scoped ENNReal
namespace BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow LpNat FarisLavine
variable {ι : Type*}
theorem summable_normSq (f : L2I ι) : Summable fun k => ‖(f : ι → ℂ) k‖ ^ 2 := by
  have h := lp.hasSum_norm (p := 2) (E := fun _ : ι => ℂ) (by norm_num) f
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at h
  simpa [Real.rpow_natCast] using h.summable

theorem memLpTwo_of_le (f : L2I ι) {g : ι → ℂ} (h : ∀ k, ‖g k‖ ≤ ‖(f : ι → ℂ) k‖) :
    Memℓp g 2 :=
  memLpTwo_of_summable_normSq
    (Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => by nlinarith [norm_nonneg (g k), norm_nonneg ((f : ι → ℂ) k), h k])
      (summable_normSq f))

theorem mem_maxDom {c : ι → ℝ} {f : L2I ι} :
    f ∈ maxDom c ↔ Memℓp (fun k => (c k : ℂ) * (f : ι → ℂ) k) 2 := Iff.rfl

theorem diagMax_symmetricOn (c : ι → ℝ) : SymmetricOn (maxDom c) (diagMax c) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [RCLike.inner_apply, diagMax_coe, map_mul, Complex.conj_ofReal]
  ring

theorem diagMax_hasSum_quadForm (c : ι → ℝ) (x : maxDom c) :
    HasSum (fun k => c k * ‖((x : L2I ι) : ι → ℂ) k‖ ^ 2) (quadForm (diagMax c) x) := by
  have h := Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) ((x : L2I ι)) (diagMax c x))
  refine h.congr_fun fun k => ?_
  have hcc : (starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) k) * ((x : L2I ι) : ι → ℂ) k
      = ((‖((x : L2I ι) : ι → ℂ) k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    norm_cast
  have hz : (inner ℂ (((x : L2I ι) : ι → ℂ) k) (((diagMax c x : L2I ι) : ι → ℂ) k) : ℂ)
      = ((c k * ‖((x : L2I ι) : ι → ℂ) k‖ ^ 2 : ℝ) : ℂ) := by
    have hstep : (inner ℂ (((x : L2I ι) : ι → ℂ) k) (((diagMax c x : L2I ι) : ι → ℂ) k) : ℂ)
        = (c k : ℂ) * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) k) * ((x : L2I ι) : ι → ℂ) k) := by
      simp only [RCLike.inner_apply, diagMax_coe]
      ring
    rw [hstep, hcc, ← Complex.ofReal_mul]
  rw [hz, Complex.ofReal_re]

theorem diagMax_quadForm_nonneg (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (x : maxDom c) :
    0 ≤ quadForm (diagMax c) x := by
  refine (diagMax_hasSum_quadForm c x).nonneg fun k => ?_
  exact mul_nonneg (hc k) (sq_nonneg _)

theorem diagMax_quadForm_ge_norm_sq (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k) (x : maxDom c) :
    ‖(x : L2I ι)‖ ^ 2 ≤ quadForm (diagMax c) x := by
  have hnorm := lp.hasSum_norm (p := 2) (E := fun _ : ι => ℂ) (by norm_num) ((x : L2I ι))
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at hnorm
  simp only [Real.rpow_natCast] at hnorm
  refine hasSum_le (fun k => ?_) hnorm (diagMax_hasSum_quadForm c x)
  nlinarith [sq_nonneg ‖((x : L2I ι) : ι → ℂ) k‖, hc k]

theorem diagMax_add_one_surjective (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (f : L2I ι) :
    ∃ x : maxDom c, (diagMax c x : L2I ι) + (x : L2I ι) = f := by
  have hpos : ∀ k, (1 : ℝ) ≤ c k + 1 := fun k => by linarith [hc k]
  have hne : ∀ k, ((c k : ℂ) + 1) ≠ 0 := by
    intro k h
    have : (c k : ℝ) + 1 = 0 := by
      have := congrArg Complex.re h
      simpa using this
    linarith [hc k]
  set g : ι → ℂ := fun k => ((f : ι → ℂ) k) / ((c k : ℂ) + 1) with hg
  have hgle : ∀ k, ‖g k‖ ≤ ‖(f : ι → ℂ) k‖ := by
    intro k
    have hnorm : ‖((c k : ℂ) + 1)‖ = c k + 1 := by
      have hre : ((c k : ℂ) + 1) = ((c k + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hre, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hc k])]
    rw [hg]
    simp only [norm_div, hnorm]
    rw [div_le_iff₀ (by linarith [hpos k])]
    nlinarith [norm_nonneg ((f : ι → ℂ) k), hc k]
  have hgmem : Memℓp g 2 := memLpTwo_of_le f hgle
  have hcgle : ∀ k, ‖(c k : ℂ) * g k‖ ≤ ‖(f : ι → ℂ) k‖ := by
    intro k
    have hnm : ‖(c k : ℂ) * g k‖ = c k * ‖g k‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hc k)]
    rw [hnm]
    have hle := hgle k
    have hnn : 0 ≤ ‖g k‖ := norm_nonneg _
    have hcg : ‖g k‖ * (c k + 1) ≤ ‖(f : ι → ℂ) k‖ * 1 := by
      have hgk : ‖g k‖ * (c k + 1) ≤ ‖(f : ι → ℂ) k‖ := by
        have hnorm : ‖((c k : ℂ) + 1)‖ = c k + 1 := by
          have hre : ((c k : ℂ) + 1) = ((c k + 1 : ℝ) : ℂ) := by push_cast; ring
          rw [hre, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hc k])]
        rw [hg]
        simp only [norm_div, hnorm]
        rw [div_mul_cancel₀]
        linarith [hpos k]
      linarith
    nlinarith [hle, hnn, hc k]
  refine ⟨⟨⟨g, hgmem⟩, memLpTwo_of_le f hcgle⟩, ?_⟩
  refine lp.ext (funext fun k => ?_)
  simp only [lp.coeFn_add, Pi.add_apply, diagMax_coe]
  change (c k : ℂ) * g k + g k = (f : ι → ℂ) k
  have : (c k : ℂ) * g k + g k = ((c k : ℂ) + 1) * g k := by ring
  rw [this, hg]
  simp only
  rw [mul_comm, div_mul_cancel₀ _ (hne k)]

theorem coe_sum_single [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) (k : ι) :
    ((∑ i ∈ S, lp.single 2 i (u i) : L2I ι) : ι → ℂ) k = if k ∈ S then u k else 0 := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply, ih]
      by_cases hka : k = a
      · subst hka
        simp [ha]
      · simp [hka, Finset.mem_insert]

theorem sum_single_mem_finiteModes [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) :
    (∑ i ∈ S, lp.single 2 i (u i) : L2I ι) ∈ lpFiniteModes ι :=
  Submodule.sum_mem _ fun i _ => lpSingle_mem_lpFiniteModes i (u i)

theorem exists_finiteModes_graph_approx (c : ι → ℝ) (x : maxDom c) (ε : ℝ) (hε : 0 < ε) :
    ∃ y : maxDom c, (y : L2I ι) ∈ lpFiniteModes ι ∧
      ‖(y : L2I ι) - (x : L2I ι)‖ < ε ∧ ‖diagMax c y - diagMax c x‖ < ε := by
  classical
  set u : ι → ℂ := fun k => ((x : L2I ι) : ι → ℂ) k with hu
  set v : ι → ℂ := fun k => ((diagMax c x : L2I ι) : ι → ℂ) k with hv
  have hxsum : HasSum (fun i => lp.single 2 i (u i)) ((x : L2I ι)) :=
    lp.hasSum_single (by norm_num) _
  have hvsum : HasSum (fun i => lp.single 2 i (v i)) ((diagMax c x : L2I ι)) :=
    lp.hasSum_single (by norm_num) _
  have hx1 : ∀ᶠ S : Finset ι in Filter.atTop,
      ‖(∑ i ∈ S, lp.single 2 i (u i) : L2I ι) - (x : L2I ι)‖ < ε := by
    have hmet := Metric.tendsto_atTop.mp hxsum
    obtain ⟨S₀, hS₀⟩ := hmet ε hε
    filter_upwards [Filter.eventually_ge_atTop S₀] with S hS
    have := hS₀ S hS
    rwa [dist_eq_norm] at this
  have hx2 : ∀ᶠ S : Finset ι in Filter.atTop,
      ‖(∑ i ∈ S, lp.single 2 i (v i) : L2I ι) - (diagMax c x : L2I ι)‖ < ε := by
    have hmet := Metric.tendsto_atTop.mp hvsum
    obtain ⟨S₀, hS₀⟩ := hmet ε hε
    filter_upwards [Filter.eventually_ge_atTop S₀] with S hS
    have := hS₀ S hS
    rwa [dist_eq_norm] at this
  obtain ⟨S, hS1, hS2⟩ := (hx1.and hx2).exists
  refine ⟨⟨(∑ i ∈ S, lp.single 2 i (u i) : L2I ι),
    finiteModes_le_maxDom c (sum_single_mem_finiteModes S u)⟩,
    sum_single_mem_finiteModes S u, hS1, ?_⟩
  have hdiag : (diagMax c ⟨(∑ i ∈ S, lp.single 2 i (u i) : L2I ι),
      finiteModes_le_maxDom c (sum_single_mem_finiteModes S u)⟩ : L2I ι)
      = (∑ i ∈ S, lp.single 2 i (v i) : L2I ι) := by
    refine lp.ext (funext fun k => ?_)
    rw [diagMax_coe, coe_sum_single, coe_sum_single]
    by_cases hk : k ∈ S
    · simp [hk, hv, hu]
    · simp [hk]
  rw [hdiag]
  exact hS2

theorem commForm_self (c : ι → ℝ) (x : maxDom c) : commForm (diagMax c) (diagMax c) x = 0 := by
  rw [commForm_eq]
  have him : (inner ℂ (diagMax c x) (diagMax c x) : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) ((diagMax c x))
  rw [him]
  ring

theorem diagMax_essentiallySelfAdjointOn (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (maxDom c) (diagMax c) :=
  essentiallySelfAdjointOn_of_farisLavine (diagMax c) (diagMax c) 0
    (diagMax_symmetricOn c) (diagMax_symmetricOn c) le_rfl (diagMax_quadForm_nonneg c hc)
    (diagMax_add_one_surjective c hc)
    (fun x => by rw [commForm_self]; simp)

theorem ikebeKato_momentum (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((diagMax c).comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by
  refine essentiallySelfAdjointOn_core_of_farisLavine (finiteModes_le_maxDom c)
    (diagMax c) (diagMax c) 1 0 0 (diagMax_symmetricOn c) (diagMax_symmetricOn c) le_rfl
    (diagMax_quadForm_nonneg c hc) (diagMax_add_one_surjective c hc)
    (fun x => by rw [commForm_self]; simp)
    (fun x => by simp) ?_
  intro x ε hε
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_finiteModes_graph_approx c x ε hε
  exact ⟨y, hy1, hy2, hy3⟩

theorem essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
    (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H : maxDom c →ₗ[ℂ] L2I ι) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom c) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom c, ‖H x‖ ^ 2 ≤ a * ‖diagMax c x‖ ^ 2 + b * ‖(x : L2I ι)‖ ^ 2)
    (hcomm : ∀ x : maxDom c, |commForm H (diagMax c) x| ≤ cst * quadForm (diagMax c) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by
  refine essentiallySelfAdjointOn_core_of_farisLavine (finiteModes_le_maxDom c)
    H (diagMax c) a b cst hH (diagMax_symmetricOn c) hcst (diagMax_quadForm_nonneg c hc)
    (diagMax_add_one_surjective c hc) hcomm hrel ?_
  intro x ε hε
  obtain ⟨y, hy1, hy2, hy3⟩ := exists_finiteModes_graph_approx c x ε hε
  exact ⟨y, hy1, hy2, hy3⟩

end BookProof.NavierStokesFlow.IkebeKato
namespace BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow LpNat FarisLavine IkebeKato
variable {ι : Type*} (S : ShiftData ι)
theorem amp_le_symbol (β : ι) : S.amp β ≤ (1 / 4 + S.K) * S.sym β := by
  have h1 := S.amp_le β
  have h2 := S.sym_ge_one β
  nlinarith [S.K_nonneg]

theorem hop_mul (g : ι → ℂ) (Y : ι → ℂ) (β : ι) :
    S.hop g β * Y β = S.hop (fun α => g α * Y (S.shift α)) β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    rw [hop_shift, hop_shift]
  · rw [hop_eq_zero S g hb, hop_eq_zero S _ hb, zero_mul]

theorem mul_hop (g : ι → ℂ) (Y : ι → ℂ) (β : ι) :
    Y β * S.hop g β = S.hop (fun α => Y (S.shift α) * g α) β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    rw [hop_shift, hop_shift]
  · rw [hop_eq_zero S g hb, hop_eq_zero S _ hb, mul_zero]

theorem conj_hop (g : ι → ℂ) (β : ι) :
    (starRingEnd ℂ) (S.hop g β) = S.hop (fun α => (starRingEnd ℂ) (g α)) β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    rw [hop_shift, hop_shift]
  · rw [hop_eq_zero S g hb, hop_eq_zero S _ hb, map_zero]

theorem tsum_ampSeq_sq_le (x : maxDom S.sym) :
    (∑' β, (S.ampSeq ((x : L2I ι) : ι → ℂ) β) ^ 2)
      ≤ (1 / 8) * ‖(diagMax S.sym x : L2I ι)‖ ^ 2 + (2 * S.K ^ 2) * ‖(x : L2I ι)‖ ^ 2 := by
  refine le_trans (Summable.tsum_le_tsum (ampSeq_sq_le S x) (summable_ampSeq_sq S x)
    (hasSum_ampBound S x).summable) ?_
  exact le_of_eq (hasSum_ampBound S x).tsum_eq

theorem summable_ampOcc (x : maxDom S.sym) :
    Summable (fun β => S.amp β * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun β => mul_nonneg (S.amp_nonneg β) (sq_nonneg _))
    (fun β => ?_) ((diagMax_hasSum_quadForm S.sym x).summable.mul_left (1 / 4 + S.K))
  nlinarith [amp_le_symbol S β, sq_nonneg ‖((x : L2I ι) : ι → ℂ) β‖]

theorem tsum_ampOcc_le (x : maxDom S.sym) :
    (∑' β, S.amp β * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2)
      ≤ (1 / 4 + S.K) * quadForm (diagMax S.sym) x := by
  have hq := diagMax_hasSum_quadForm S.sym x
  refine le_trans (Summable.tsum_le_tsum (fun β => ?_) (summable_ampOcc S x)
    (hq.summable.mul_left (1 / 4 + S.K))) ?_
  · nlinarith [amp_le_symbol S β, sq_nonneg ‖((x : L2I ι) : ι → ℂ) β‖]
  · exact le_of_eq (hq.mul_left (1 / 4 + S.K)).tsum_eq

theorem abs_le_of_hasSum {f g : ι → ℝ} {A B : ℝ} (hf : HasSum f A) (hg : HasSum g B)
    (h : ∀ β, |f β| ≤ g β) : |A| ≤ B := by
  refine abs_le.mpr ⟨?_, hasSum_le (fun β => le_trans (le_abs_self _) (h β)) hf hg⟩
  have hneg : HasSum (fun β => -g β) (-B) := hg.neg
  have := hasSum_le (fun β => by linarith [neg_abs_le (f β), h β] : ∀ β, -g β ≤ f β) hneg hf
  linarith

end BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
namespace BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow LpNat FarisLavine IkebeKato
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
theorem commForm_add (H₁ H₂ N : D →ₗ[ℂ] F) (x : D) :
    commForm (H₁ + H₂) N x = commForm H₁ N x + commForm H₂ N x := by
  simp only [commForm, LinearMap.add_apply, inner_add_left, inner_add_right]
  have : Complex.I * (inner ℂ (H₁ x) (N x) + inner ℂ (H₂ x) (N x)
      - (inner ℂ (N x) (H₁ x) + inner ℂ (N x) (H₂ x)))
      = Complex.I * (inner ℂ (H₁ x) (N x) - inner ℂ (N x) (H₁ x))
        + Complex.I * (inner ℂ (H₂ x) (N x) - inner ℂ (N x) (H₂ x)) := by ring
  rw [this, Complex.add_re]

end BookProof.NavierStokesFlow.AffineFiber

namespace BookProof.NavierStokesFlow.HermiteFarisLavine
open BookProof.NavierStokesFlow LpNat FarisLavine IkebeKato
variable {κ : ℝ}
@[simp] theorem shift2_zero_apply {M : Type*} [Zero M] (g : ℕ → M) : shift2 g 0 = 0 := rfl

@[simp] theorem shift2_one_apply {M : Type*} [Zero M] (g : ℕ → M) : shift2 g 1 = 0 := rfl

theorem amp_le_symbol (hκ : 0 ≤ κ) (n : ℕ) :
    amp κ n ≤ (1 / 4 + κ / 2) * oscSymbol κ n := by
  have h1 := amp_le_quarter hκ n
  have h2 : (1 : ℝ) ≤ oscSymbol κ n := oscSymbol_ge_one hκ n
  nlinarith

theorem tsum_ampSeq_sq_le (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    (∑' n, (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2)
      ≤ (1 / 8) * ‖(diagMax (oscSymbol κ) x : L2I ℕ)‖ ^ 2 + (κ ^ 2 / 2) * ‖(x : L2I ℕ)‖ ^ 2 := by
  refine le_trans (Summable.tsum_le_tsum (ampSeq_sq_le hκ x) (summable_ampSeq_sq hκ x)
    (hasSum_ampBound x).summable) ?_
  exact le_of_eq (hasSum_ampBound x).tsum_eq

@[simp] theorem nsH_coe (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (m : ℕ) :
    ((nsH κ hκ x : L2I ℕ) : ℕ → ℂ) m = hFun κ ((x : L2I ℕ) : ℕ → ℂ) m := rfl

theorem norm_crossA (hκ : 0 ≤ κ) (X Y : ℕ → ℂ) (n : ℕ) :
    ‖crossA κ X Y n‖ = ampSeq κ X n * ‖Y (n + 2)‖ := by
  simp only [crossA, ampSeq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (amp_nonneg hκ n), RCLike.norm_conj]

theorem norm_crossB (hκ : 0 ≤ κ) (X Y : ℕ → ℂ) (n : ℕ) :
    ‖crossB κ X Y n‖ = amp κ n * ‖X (n + 2)‖ * ‖Y n‖ := by
  simp only [crossB, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (amp_nonneg hκ n), RCLike.norm_conj]

theorem summable_crossA (hκ : 0 ≤ κ) {X Y : ℕ → ℂ}
    (hX : Summable fun n => (ampSeq κ X n) ^ 2) (hY : Summable fun n => ‖Y n‖ ^ 2) :
    Summable (crossA κ X Y) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((hX.add ((summable_nat_add_iff 2).mpr hY)).mul_left (1 / 2)))
  rw [norm_crossA hκ]
  nlinarith [sq_nonneg (ampSeq κ X n - ‖Y (n + 2)‖), ampSeq_nonneg hκ X n, norm_nonneg (Y (n + 2))]

theorem summable_crossB (hκ : 0 ≤ κ) {X Y : ℕ → ℂ}
    (hX : Summable fun n => (ampSeq κ X n) ^ 2) (hY : Summable fun n => ‖Y n‖ ^ 2) :
    Summable (crossB κ X Y) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((((summable_nat_add_iff 2).mpr hX).add hY).mul_left (1 / 2)))
  rw [norm_crossB hκ]
  have hmono : amp κ n * ‖X (n + 2)‖ ≤ ampSeq κ X (n + 2) :=
    mul_le_mul_of_nonneg_right (amp_le_amp_add_two hκ n) (norm_nonneg _)
  have h0 : 0 ≤ ‖Y n‖ := norm_nonneg _
  nlinarith [sq_nonneg (ampSeq κ X (n + 2) - ‖Y n‖), ampSeq_nonneg hκ X (n + 2),
    mul_le_mul_of_nonneg_right hmono h0]

theorem conj_hFun_mul (κ : ℝ) (X Y : ℕ → ℂ) (m : ℕ) :
    (starRingEnd ℂ) (hFun κ X m) * Y m
      = -Complex.I * shift2 (crossA κ X Y) m + Complex.I * crossB κ X Y m := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;>
      simp [hFun, crossB, shift2, Complex.ext_iff] <;>
      constructor <;> ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    simp only [hFun, crossA, crossB, shift2_add_two, map_mul, Complex.conj_I,
      Complex.conj_ofReal, map_sub]
    ring

theorem conj_mul_hFun (κ : ℝ) (X Y : ℕ → ℂ) (m : ℕ) :
    (starRingEnd ℂ) (X m) * hFun κ Y m
      = -Complex.I * crossA κ X Y m + Complex.I * shift2 (crossB κ X Y) m := by
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;>
      simp [hFun, crossA, shift2, Complex.ext_iff] <;>
      constructor <;> ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    simp only [hFun, crossA, crossB, shift2_add_two]
    ring

theorem hasSum_inner_nsH_left (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (y : L2I ℕ) :
    HasSum (fun n => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) ((y : ℕ → ℂ)) n
        + Complex.I * crossB κ ((x : L2I ℕ) : ℕ → ℂ) ((y : ℕ → ℂ)) n)
      (inner ℂ (nsH κ hκ x : L2I ℕ) y) := by
  have hA := summable_crossA (Y := (y : ℕ → ℂ)) hκ (summable_ampSeq_sq hκ x) (summable_normSq y)
  have hB := summable_crossB (Y := (y : ℕ → ℂ)) hκ (summable_ampSeq_sq hκ x) (summable_normSq y)
  have hgoal := (hA.hasSum.mul_left (-Complex.I)).add (hB.hasSum.mul_left Complex.I)
  have hshift := ((hasSum_shift2_iff.mpr hA.hasSum).mul_left (-Complex.I)).add
    (hB.hasSum.mul_left Complex.I)
  have hinner := lp.hasSum_inner (𝕜 := ℂ) ((nsH κ hκ x : L2I ℕ)) y
  have heq : (fun m => (inner ℂ (((nsH κ hκ x : L2I ℕ) : ℕ → ℂ) m) ((y : ℕ → ℂ) m) : ℂ))
      = fun m => -Complex.I * shift2 (crossA κ ((x : L2I ℕ) : ℕ → ℂ) ((y : ℕ → ℂ))) m
          + Complex.I * crossB κ ((x : L2I ℕ) : ℕ → ℂ) ((y : ℕ → ℂ)) m := by
    funext m
    rw [RCLike.inner_apply, nsH_coe, mul_comm]
    exact conj_hFun_mul κ _ _ m
  rw [heq] at hinner
  rwa [hshift.unique hinner] at hgoal

theorem hasSum_inner_nsH_right (hκ : 0 ≤ κ) (x y : maxDom (oscSymbol κ)) :
    HasSum (fun n => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) n
        + Complex.I * crossB κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) n)
      (inner ℂ (x : L2I ℕ) (nsH κ hκ y : L2I ℕ)) := by
  have hA := summable_crossA (Y := ((y : L2I ℕ) : ℕ → ℂ)) hκ (summable_ampSeq_sq hκ x)
    (summable_normSq (y : L2I ℕ))
  have hB := summable_crossB (Y := ((y : L2I ℕ) : ℕ → ℂ)) hκ (summable_ampSeq_sq hκ x)
    (summable_normSq (y : L2I ℕ))
  have hgoal := (hA.hasSum.mul_left (-Complex.I)).add (hB.hasSum.mul_left Complex.I)
  have hshift := (hA.hasSum.mul_left (-Complex.I)).add
    ((hasSum_shift2_iff.mpr hB.hasSum).mul_left Complex.I)
  have hinner := lp.hasSum_inner (𝕜 := ℂ) ((x : L2I ℕ)) ((nsH κ hκ y : L2I ℕ))
  have heq : (fun m => (inner ℂ (((x : L2I ℕ) : ℕ → ℂ) m)
        (((nsH κ hκ y : L2I ℕ) : ℕ → ℂ) m) : ℂ))
      = fun m => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) m
          + Complex.I * shift2 (crossB κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ))) m := by
    funext m
    rw [RCLike.inner_apply, nsH_coe, mul_comm]
    exact conj_mul_hFun κ _ _ m
  rw [heq] at hinner
  rwa [hshift.unique hinner] at hgoal

theorem nsH_symmetricOn (hκ : 0 ≤ κ) : SymmetricOn (maxDom (oscSymbol κ)) (nsH κ hκ) := by
  intro x y
  exact (hasSum_inner_nsH_left hκ x (y : L2I ℕ)).unique (hasSum_inner_nsH_right hκ x y)

theorem normSq_hFun_le (hκ : 0 ≤ κ) (X : ℕ → ℂ) (m : ℕ) :
    ‖hFun κ X m‖ ^ 2
      ≤ 2 * shift2 (fun n => (ampSeq κ X n) ^ 2) m + 2 * (ampSeq κ X (m + 2)) ^ 2 := by
  have h1 := norm_hFun_le hκ X m
  have h2 : 0 ≤ shift2 (ampSeq κ X) m := shift2_nonneg _ (ampSeq_nonneg hκ _) m
  have h3 : 0 ≤ ampSeq κ X (m + 2) := ampSeq_nonneg hκ _ _
  have h4 := mul_self_le_mul_self (norm_nonneg (hFun κ X m)) h1
  rw [shift2_sq]
  nlinarith [h4, sq_nonneg (shift2 (ampSeq κ X) m - ampSeq κ X (m + 2))]

theorem tsum_shift_le {f : ℕ → ℝ} (hf : Summable f) (hnn : ∀ n, 0 ≤ f n) :
    (∑' n, f (n + 2)) ≤ ∑' n, f n := by
  have h := hf.sum_add_tsum_nat_add 2
  have h0 : 0 ≤ ∑ i ∈ Finset.range 2, f i := Finset.sum_nonneg fun i _ => hnn i
  linarith [h]

theorem nsH_relative_bound (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    ‖(nsH κ hκ x : L2I ℕ)‖ ^ 2
      ≤ (1 / 2) * ‖(diagMax (oscSymbol κ) x : L2I ℕ)‖ ^ 2 + (2 * κ ^ 2) * ‖(x : L2I ℕ)‖ ^ 2 := by
  have hS := summable_ampSeq_sq hκ x
  have hshift : Summable (shift2 (fun n => (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2)) :=
    summable_shift2 hS
  have htail : Summable (fun m => (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) (m + 2)) ^ 2) :=
    (summable_nat_add_iff 2).mpr hS
  have hbound := (hshift.hasSum.mul_left 2).add (htail.hasSum.mul_left 2)
  have hle : ‖(nsH κ hκ x : L2I ℕ)‖ ^ 2
      ≤ 2 * (∑' m, shift2 (fun n => (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2) m)
        + 2 * ∑' m, (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) (m + 2)) ^ 2 := by
    refine hasSum_le (fun m => ?_) (hasSum_normSq (nsH κ hκ x : L2I ℕ)) hbound
    rw [nsH_coe]
    exact normSq_hFun_le hκ _ m
  have hshifteq : (∑' m, shift2 (fun n => (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2) m)
      = ∑' n, (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2 :=
    (hasSum_shift2_iff.mpr hS.hasSum).tsum_eq
  have htaille : (∑' m, (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) (m + 2)) ^ 2)
      ≤ ∑' n, (ampSeq κ ((x : L2I ℕ) : ℕ → ℂ) n) ^ 2 :=
    tsum_shift_le hS (fun n => sq_nonneg _)
  have hT := tsum_ampSeq_sq_le hκ x
  rw [hshifteq] at hle
  linarith

theorem hasSum_commForm (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    HasSum (fun n => 8 * κ * (amp κ n
        * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n) * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re))
      (commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x) := by
  have hL := hasSum_inner_nsH_left hκ x (diagMax (oscSymbol κ) x : L2I ℕ)
  have hIm := Complex.hasSum_im hL
  have hpt : ∀ n, (-Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ)
        (((diagMax (oscSymbol κ) x : L2I ℕ) : ℕ → ℂ)) n
      + Complex.I * crossB κ ((x : L2I ℕ) : ℕ → ℂ)
        (((diagMax (oscSymbol κ) x : L2I ℕ) : ℕ → ℂ)) n).im
      = -(4 * κ) * (amp κ n
        * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n) * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re) := by
    intro n
    simp only [crossA, crossB, diagMax_coe, oscSymbol_step]
    simp [Complex.add_im, Complex.mul_im, Complex.mul_re]
    ring
  have hIm' : HasSum (fun n => -(4 * κ) * (amp κ n
      * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n) * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re))
      (inner ℂ (nsH κ hκ x : L2I ℕ) (diagMax (oscSymbol κ) x : L2I ℕ) : ℂ).im := by
    refine hIm.congr_fun ?_
    intro n
    exact (hpt n).symm
  have hres := hIm'.mul_left (-2)
  rw [commForm_eq]
  refine hres.congr_fun ?_
  intro n
  ring

theorem summable_ampOcc (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    Summable (fun n => amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (amp_nonneg hκ n) (sq_nonneg _))
    (fun n => ?_) ((diagMax_hasSum_quadForm (oscSymbol κ) x).summable.mul_left (1 / 4 + κ / 2))
  nlinarith [amp_le_symbol hκ n, sq_nonneg ‖((x : L2I ℕ) : ℕ → ℂ) n‖]

theorem tsum_ampOcc_le (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    (∑' n, amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2)
      ≤ (1 / 4 + κ / 2) * quadForm (diagMax (oscSymbol κ)) x := by
  have hq := diagMax_hasSum_quadForm (oscSymbol κ) x
  refine le_trans (Summable.tsum_le_tsum (fun n => ?_) (summable_ampOcc hκ x)
    (hq.summable.mul_left (1 / 4 + κ / 2))) ?_
  · nlinarith [amp_le_symbol hκ n, sq_nonneg ‖((x : L2I ℕ) : ℕ → ℂ) n‖]
  · exact le_of_eq (hq.mul_left (1 / 4 + κ / 2)).tsum_eq

theorem abs_le_of_hasSum {f g : ℕ → ℝ} {S T : ℝ} (hf : HasSum f S) (hg : HasSum g T)
    (h : ∀ n, |f n| ≤ g n) : |S| ≤ T := by
  refine abs_le.mpr ⟨?_, hasSum_le (fun n => le_trans (le_abs_self _) (h n)) hf hg⟩
  have hneg : HasSum (fun n => -g n) (-T) := hg.neg
  have := hasSum_le (fun n => by linarith [neg_abs_le (f n), h n] : ∀ n, -g n ≤ f n) hneg hf
  linarith

theorem nsH_commForm_bound (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) :
    |commForm (nsH κ hκ) (diagMax (oscSymbol κ)) x|
      ≤ (2 * κ + 4 * κ ^ 2) * quadForm (diagMax (oscSymbol κ)) x := by
  have hus := summable_ampOcc hκ x
  have hutail : Summable (fun n => amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2) :=
    (summable_nat_add_iff 2).mpr hus
  have hbound : HasSum (fun n => 4 * κ * (amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2
      + amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2))
      (4 * κ * ((∑' n, amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2)
        + ∑' n, amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2)) :=
    (hus.hasSum.add hutail.hasSum).mul_left (4 * κ)
  have hptle : ∀ n, |8 * κ * (amp κ n * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
        * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re)|
      ≤ 4 * κ * (amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2
        + amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2) := by
    intro n
    have hamp : 0 ≤ amp κ n := amp_nonneg hκ n
    have hre : |((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
        * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re|
        ≤ ‖((x : L2I ℕ) : ℕ → ℂ) n‖ * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      rw [norm_mul, RCLike.norm_conj]
    have habs : |8 * κ * (amp κ n * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
          * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re)|
        = 8 * κ * amp κ n * |((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
          * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re| := by
      rw [show (8 : ℝ) * κ * (amp κ n * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
          * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re)
          = (8 * κ * amp κ n) * ((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
            * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re from by ring, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 8 * κ * amp κ n)]
    have h1 : 8 * κ * amp κ n * |((starRingEnd ℂ) (((x : L2I ℕ) : ℕ → ℂ) n)
          * ((x : L2I ℕ) : ℕ → ℂ) (n + 2)).re|
        ≤ 8 * κ * amp κ n * (‖((x : L2I ℕ) : ℕ → ℂ) n‖ * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖) :=
      mul_le_mul_of_nonneg_left hre (by positivity)
    have hkey : 8 * κ * amp κ n * (‖((x : L2I ℕ) : ℕ → ℂ) n‖ * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖)
        ≤ 4 * κ * (amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2
          + amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2) := by
      have h2ab : 2 * (‖((x : L2I ℕ) : ℕ → ℂ) n‖ * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖)
          ≤ ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2 + ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖((x : L2I ℕ) : ℕ → ℂ) n‖ - ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖)]
      have := mul_le_mul_of_nonneg_left h2ab
        (show (0 : ℝ) ≤ 4 * κ * amp κ n by positivity)
      linarith [this]
    have hmono : 4 * κ * (amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2)
        ≤ 4 * κ * (amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (amp_le_amp_add_two hκ n) (sq_nonneg _)) (by positivity)
    rw [habs]
    linarith
  have habs := abs_le_of_hasSum (hasSum_commForm hκ x) hbound hptle
  have htail : (∑' n, amp κ (n + 2) * ‖((x : L2I ℕ) : ℕ → ℂ) (n + 2)‖ ^ 2)
      ≤ ∑' n, amp κ n * ‖((x : L2I ℕ) : ℕ → ℂ) n‖ ^ 2 :=
    tsum_shift_le hus (fun n => mul_nonneg (amp_nonneg hκ n) (sq_nonneg _))
  have hU := tsum_ampOcc_le hκ x
  have hqf : 0 ≤ quadForm (diagMax (oscSymbol κ)) x :=
    diagMax_quadForm_nonneg _ (oscSymbol_nonneg hκ) x
  refine le_trans habs ?_
  nlinarith [hU, htail, hκ]

theorem nsH_essentiallySelfAdjointOn_core (hκ : 0 ≤ κ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((nsH κ hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ)))) :=
  essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds (oscSymbol κ)
    (oscSymbol_nonneg hκ) (nsH κ hκ) (1 / 2) (2 * κ ^ 2) (2 * κ + 4 * κ ^ 2)
    (nsH_symmetricOn hκ) (by positivity) (nsH_relative_bound hκ) (nsH_commForm_bound hκ)

end BookProof.NavierStokesFlow.HermiteFarisLavine
namespace BookProof.NavierStokesFlow.HermiteCanonical
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
variable {κ : ℝ}
@[simp] theorem ann_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((ann x : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (Real.sqrt (n + 1) : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n + 1) := rfl

@[simp] theorem cre_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((cre x : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (Real.sqrt n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) (n - 1) := rfl

theorem sqrt_mul_sqrt (r : ℝ) (hr : 0 ≤ r) : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr]

theorem ann_ann_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((ann (ann x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (Real.sqrt ((n : ℝ) + 1) : ℂ) * (Real.sqrt ((n : ℝ) + 2) : ℂ)
        * ((x : L2I ℕ) : ℕ → ℂ) (n + 2) := by
  rw [ann_coe, ann_coe]
  push_cast
  ring_nf

theorem cre_cre_coe_add_two (x : lpFiniteModes ℕ) (k : ℕ) :
    (((cre (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) (k + 2)
      = (Real.sqrt ((k : ℝ) + 2) : ℂ) * (Real.sqrt ((k : ℝ) + 1) : ℂ)
        * ((x : L2I ℕ) : ℕ → ℂ) k := by
  rw [cre_coe, cre_coe]
  have h1 : (k + 2 - 1) = k + 1 := by omega
  have h2 : (k + 1 - 1) = k := by omega
  rw [h1, h2]
  push_cast
  ring

theorem cre_cre_coe_zero (x : lpFiniteModes ℕ) :
    (((cre (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) 0 = 0 := by
  rw [cre_coe]
  simp

theorem cre_cre_coe_one (x : lpFiniteModes ℕ) :
    (((cre (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) 1 = 0 := by
  rw [cre_coe, cre_coe]
  simp

theorem ann_cre_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((ann (cre x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = ((n : ℂ) + 1) * ((x : L2I ℕ) : ℕ → ℂ) n := by
  rw [ann_coe, cre_coe]
  have h1 : (n + 1 - 1) = n := by omega
  rw [h1]
  push_cast
  rw [← mul_assoc, sqrt_mul_sqrt _ (by positivity)]
  push_cast
  ring

theorem cre_ann_coe (x : lpFiniteModes ℕ) (n : ℕ) :
    (((cre (ann x) : lpFiniteModes ℕ) : L2I ℕ) : ℕ → ℂ) n
      = (n : ℂ) * ((x : L2I ℕ) : ℕ → ℂ) n := by
  rw [cre_coe]
  cases n with
  | zero => simp
  | succ k =>
      rw [ann_coe]
      have h1 : (k + 1 - 1) = k := by omega
      rw [h1]
      push_cast
      rw [← mul_assoc, sqrt_mul_sqrt _ (by positivity)]
      push_cast
      ring

theorem comm_ann_cre : ann.comp cre - cre.comp ann = LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, Submodule.coe_sub,
    lp.coeFn_sub, Pi.sub_apply, ann_cre_coe, cre_ann_coe]
  ring

theorem bracket_DS :
    (cre - ann).comp (cre + ann) - (cre + ann).comp (cre - ann) = (-2 : ℂ) • LinearMap.id := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_add, map_sub, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ann_cre_coe, cre_ann_coe]
  ring

theorem sq_diff :
    (cre + ann).comp (cre + ann) - (cre - ann).comp (cre - ann)
      = (2 : ℂ) • (cre.comp ann + ann.comp cre) := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_add, map_sub, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem anti_DS :
    (cre - ann).comp (cre + ann) + (cre + ann).comp (cre - ann)
      = (2 : ℂ) • (cre.comp cre - ann.comp ann) := by
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    map_add, map_sub, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem sqrt_half_sq (hκ : 0 ≤ κ) :
    (Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ) = (κ : ℂ) / 2 := by
  rw [sqrt_mul_sqrt _ (by positivity)]
  push_cast
  ring

theorem sqrt_half_mul_inv (hκ : 0 < κ) :
    (Real.sqrt (κ / 2) : ℂ) * ((1 / Real.sqrt (2 * κ) : ℝ) : ℂ) = 1 / 2 := by
  have hreal : Real.sqrt (κ / 2) * (1 / Real.sqrt (2 * κ)) = 1 / 2 := by
    rw [Real.sqrt_div hκ.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hk : 0 < Real.sqrt κ := Real.sqrt_pos.mpr hκ
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    nlinarith [h2, hk]
  rw [← Complex.ofReal_mul, hreal]
  norm_num

theorem drift_eq (hκ : 0 < κ) : drift κ = (κ : ℂ) • pos κ := by
  rw [drift, pos, smul_smul]
  congr 1
  have hne : Real.sqrt (2 * κ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by linarith)
  have hmul : Real.sqrt (κ / 2) * Real.sqrt (2 * κ) = κ := by
    rw [← Real.sqrt_mul (by positivity)]
    have hsq : κ / 2 * (2 * κ) = κ ^ 2 := by ring
    rw [hsq, Real.sqrt_sq hκ.le]
  have hreal : Real.sqrt (κ / 2) = κ * (1 / Real.sqrt (2 * κ)) := by
    rw [eq_comm, mul_one_div, div_eq_iff hne]
    exact hmul.symm
  rw [← Complex.ofReal_mul, ← hreal]

theorem comm_mom_pos (hκ : 0 < κ) :
    (mom κ).comp (pos κ) - (pos κ).comp (mom κ) = (-Complex.I) • LinearMap.id := by
  have hs : Complex.I * (Real.sqrt (κ / 2) : ℂ) * ((1 / Real.sqrt (2 * κ) : ℝ) : ℂ) * (-2)
      = -Complex.I := by
    linear_combination (-2 * Complex.I) * sqrt_half_mul_inv hκ
  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun n => ?_))
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, mom, pos, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.add_apply, map_smul, map_add, map_sub,
    Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, lp.coeFn_sub, lp.coeFn_add,
    lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    ann_cre_coe, cre_ann_coe]
  linear_combination (((x : L2I ℕ) : ℕ → ℂ) n) * hs

theorem amp_eq_sqrt_mul (κ : ℝ) (n : ℕ) :
    amp κ n = (κ / 2) * (Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 2)) := by
  rw [amp, ← Real.sqrt_mul (by positivity)]

theorem comparison_eq (hκ : 0 ≤ κ) :
    (lpFiniteModes ℕ).subtype.comp
        ((mom κ).comp (mom κ) + (drift κ).comp (drift κ) + LinearMap.id)
      = (diagMax (oscSymbol κ)).comp
        (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ))) := by
  have hsq : (mom κ).comp (mom κ) + (drift κ).comp (drift κ)
      = (κ : ℂ) • (cre.comp ann + ann.comp cre) := by
    have h1 : (mom κ).comp (mom κ)
        = (-((Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ))) •
          (cre - ann).comp (cre - ann) := by
      simp only [mom, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
      congr 1
      have : Complex.I * Complex.I = -1 := Complex.I_mul_I
      ring_nf
      rw [Complex.I_sq]
      ring
    have h2 : (drift κ).comp (drift κ)
        = ((Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ)) • (cre + ann).comp (cre + ann) := by
      simp only [drift, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    have hexp : (cre + ann).comp (cre + ann)
        = (cre - ann).comp (cre - ann) + (2 : ℂ) • (cre.comp ann + ann.comp cre) := by
      rw [← sq_diff]
      abel
    rw [h1, h2, sqrt_half_sq hκ, hexp]
    module
  refine LinearMap.ext fun x => lp.ext (funext fun n => ?_)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, hsq, Submodule.subtype_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Submodule.coe_add, Submodule.coe_smul,
    lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, diagMax_coe,
    ann_cre_coe, cre_ann_coe, Submodule.inclusion_apply]
  simp only [oscSymbol]
  push_cast
  ring

private theorem parent_shift2_zero {M : Type*} [Zero M] (g : ℕ → M) : shift2 g 0 = 0 := rfl
private theorem parent_shift2_one {M : Type*} [Zero M] (g : ℕ → M) : shift2 g 1 = 0 := rfl
private theorem parent_nsH_coe (hκ : 0 ≤ κ) (x : maxDom (oscSymbol κ)) (m : ℕ) :
    ((nsH κ hκ x : L2I ℕ) : ℕ → ℂ) m = hFun κ (((x : L2I ℕ) : ℕ → ℂ)) m := rfl
theorem hamiltonian_eq (hκ : 0 ≤ κ) :
    (lpFiniteModes ℕ).subtype.comp
        (((1 : ℂ) / 2) • ((mom κ).comp (drift κ) + (drift κ).comp (mom κ)))
      = (nsH κ hκ).comp (Submodule.inclusion (finiteModes_le_maxDom (oscSymbol κ))) := by
  have hsym : (mom κ).comp (drift κ) + (drift κ).comp (mom κ)
      = (Complex.I * (κ : ℂ)) • (cre.comp cre - ann.comp ann) := by
    have h1 : (mom κ).comp (drift κ)
        = (Complex.I * ((Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ))) •
          (cre - ann).comp (cre + ann) := by
      simp only [mom, drift, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
      congr 1
      ring
    have h2 : (drift κ).comp (mom κ)
        = (Complex.I * ((Real.sqrt (κ / 2) : ℂ) * (Real.sqrt (κ / 2) : ℂ))) •
          (cre + ann).comp (cre - ann) := by
      simp only [mom, drift, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
      congr 1
      ring
    rw [h1, h2, ← smul_add, anti_DS, sqrt_half_sq hκ, smul_smul]
    congr 1
    ring
  refine LinearMap.ext fun x => lp.ext (funext fun m => ?_)
  simp only [LinearMap.comp_apply, hsym, Submodule.subtype_apply, LinearMap.smul_apply,
    Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, LinearMap.sub_apply,
    Submodule.coe_sub, lp.coeFn_sub, Pi.sub_apply, parent_nsH_coe, Submodule.inclusion_apply]
  rw [hFun, ann_ann_coe]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m
    · rw [cre_cre_coe_zero]
      simp only [parent_shift2_zero]
      rw [amp_eq_sqrt_mul]
      push_cast
      ring
    · rw [cre_cre_coe_one]
      simp only [parent_shift2_one]
      rw [amp_eq_sqrt_mul]
      push_cast
      ring
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    rw [cre_cre_coe_add_two, shift2_add_two, amp_eq_sqrt_mul, amp_eq_sqrt_mul]
    push_cast
    ring

end BookProof.NavierStokesFlow.HermiteCanonical

/-
Copyright2026LeonardoPedro. Adapted from timepiece61595bc.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.


   Copyright 2026 Leonardo Pedro

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/
-- Generated from ChapterNavierStokesHermiteCanonical.lean — theorem BookProof.NavierStokesFlow.HermiteCanonical.canonical_essentiallySelfAdjointOn_core
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteCanonical







open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.HermiteFarisLavine
























variable {κ : ℝ}
theorem solution (hκ : 0 ≤ κ) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((lpFiniteModes ℕ).subtype.comp
        (((1 : ℂ) / 2) • ((mom κ).comp (drift κ) + (drift κ).comp (mom κ)))) := by
  rw [hamiltonian_eq hκ]
  exact nsH_essentiallySelfAdjointOn_core hκ
#print axioms solution
