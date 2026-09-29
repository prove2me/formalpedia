-- Prove2me | solution 1 for BookProof.ChapterSirkPerSystem.ns_sirk_crouzeix_domain
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:49:13.92898+00:00
-- url     : https://prove2.me/submissions/c653add7-4efa-49ea-b7c7-210d55ab1952

import Definitions.Def_ChapterSirkPerSystem
-- Adapted prerequisite proofs: Leonardo Pedro, timepiece 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Filter Topology
namespace BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
theorem sirkNS_inner_im_swap (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_im, neg_neg]

theorem sirkNS_inner_apply_self_im (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) (x : D) :
    (inner ℂ (T x) (x : F) : ℂ).im = 0 := by
  have h := congrArg Complex.im (hT x x)
  rw [sirkNS_inner_im_swap (T x) (x : F)] at h
  linarith

theorem sirkNS_quadForm_im (N : D →ₗ[ℂ] F) (hN : SymmetricOn D N) (x : D) :
    (inner ℂ (x : F) (N x) : ℂ).im = 0 := by
  rw [sirkNS_inner_im_swap (N x) (x : F), sirkNS_inner_apply_self_im N hN x, neg_zero]

theorem sirkNS_commForm_eq (H N : D →ₗ[ℂ] F) (x : D) :
    commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im := by
  rw [commForm, Complex.mul_re]
  simp [Complex.sub_im, sirkNS_inner_im_swap (H x) (N x)]
  ring

theorem sirkNS_deficiencyTrivialAt_of_farisLavine
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
  have hBim : (inner ℂ (H g) (g : F) : ℂ).im = 0 := sirkNS_inner_apply_self_im H hH g
  have hPim : (inner ℂ (g : F) (N g) : ℂ).im = 0 := sirkNS_quadForm_im N hN g
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
    rw [sirkNS_commForm_eq, hAim, abs_mul, abs_mul, abs_of_nonneg htnn]
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

theorem sirkNS_norm_sub_smul_sq (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (d : ℝ) (x : D) :
    ‖H x - ((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = ‖H x‖ ^ 2 + d ^ 2 * ‖(x : F)‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ)]
  have h1 : (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ)
      = ((d : ℂ) * Complex.I) * inner ℂ (H x) (x : F) := inner_smul_right _ _ _
  have h2 : RCLike.re (inner ℂ (H x) (((d : ℂ) * Complex.I) • (x : F)) : ℂ) = 0 := by
    rw [h1]; simp [sirkNS_inner_apply_self_im H hH x]
  have h3 : ‖((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = d ^ 2 * ‖(x : F)‖ ^ 2 := by
    rw [norm_smul]; simp [mul_pow, sq_abs]
  rw [h2, h3]; ring

theorem sirkNS_dense_range_of_deficiencyTrivialAt [CompleteSpace F] (H : D →ₗ[ℂ] F) (w₀ : ℂ)
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

theorem sirkNS_exists_weak_graph_limit [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H)
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
    have hsq := sirkNS_norm_sub_smul_sq H hH d (x m - x n)
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
      fun n => sirkNS_inner_apply_self_im H hH (x n)
    simp only [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds

theorem sirkNS_deficiencyTrivialAt_of_dense_range [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (e : ℝ) (he : e ≠ 0) (σ : ℂ) (hσ : σ.im ≠ 0)
    (hdense : Dense (Set.range fun x : D => H x - ((e : ℂ) * Complex.I) • (x : F)))
    (hdef : DeficiencyTrivialAt D H ((e : ℂ) * Complex.I)) :
    DeficiencyTrivialAt D H σ := by
  intro w hw
  obtain ⟨u, z, hu, hzy, him⟩ :=
    sirkNS_exists_weak_graph_limit H hH e he hdense ((σ - (e : ℂ) * Complex.I) • w)
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

theorem sirkNS_essentiallySelfAdjointOn_of_farisLavine [CompleteSpace F]
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
    sirkNS_deficiencyTrivialAt_of_farisLavine H N c d hH hN hc hNpos hNsurj hcomm hdgt
  have hminus : DeficiencyTrivialAt D H (((-d : ℝ) : ℂ) * Complex.I) := by
    refine sirkNS_deficiencyTrivialAt_of_farisLavine H N c (-d) hH hN hc hNpos hNsurj hcomm ?_
    rwa [abs_neg]
  have hconj : starRingEnd ℂ ((d : ℂ) * Complex.I) = ((-d : ℝ) : ℂ) * Complex.I := by
    simp
  have hdense : Dense (Set.range fun x : D => H x - ((d : ℂ) * Complex.I) • (x : F)) :=
    sirkNS_dense_range_of_deficiencyTrivialAt H ((d : ℂ) * Complex.I) (by rw [hconj]; exact hminus)
  exact ⟨sirkNS_deficiencyTrivialAt_of_dense_range H hH d hd0 Complex.I (by simp) hdense hplus,
    sirkNS_deficiencyTrivialAt_of_dense_range H hH d hd0 (-Complex.I) (by simp) hdense hplus⟩

theorem sirkNS_essentiallySelfAdjointOn_top_of_symmetric [CompleteSpace F]
    (H : (⊤ : Submodule ℂ F) →ₗ[ℂ] F) (hH : SymmetricOn ⊤ H) :
    EssentiallySelfAdjointOn (⊤ : Submodule ℂ F) H := by
  refine sirkNS_essentiallySelfAdjointOn_of_farisLavine H (⊤ : Submodule ℂ F).subtype 0 hH
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
      sirkNS_inner_apply_self_im H hH x
    rw [sirkNS_commForm_eq, h]
    simp

theorem sirkNS_essentiallySelfAdjointOn_restrict_of_graph_core
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

theorem sirkNS_essentiallySelfAdjointOn_core_of_farisLavine [CompleteSpace F]
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
  refine sirkNS_essentiallySelfAdjointOn_restrict_of_graph_core hCD H (fun x ε hε => ?_)
    (sirkNS_essentiallySelfAdjointOn_of_farisLavine H N c hH hN hc hNpos hNsurj hcomm)
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
theorem sirkNS_summable_normSq (f : L2I ι) : Summable fun k => ‖(f : ι → ℂ) k‖ ^ 2 := by
  have h := lp.hasSum_norm (p := 2) (E := fun _ : ι => ℂ) (by norm_num) f
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at h
  simpa [Real.rpow_natCast] using h.summable

theorem sirkNS_memLpTwo_of_le (f : L2I ι) {g : ι → ℂ} (h : ∀ k, ‖g k‖ ≤ ‖(f : ι → ℂ) k‖) :
    Memℓp g 2 :=
  memLpTwo_of_summable_normSq
    (Summable.of_nonneg_of_le (fun k => sq_nonneg _)
      (fun k => by nlinarith [norm_nonneg (g k), norm_nonneg ((f : ι → ℂ) k), h k])
      (sirkNS_summable_normSq f))

theorem sirkNS_mem_maxDom {c : ι → ℝ} {f : L2I ι} :
    f ∈ maxDom c ↔ Memℓp (fun k => (c k : ℂ) * (f : ι → ℂ) k) 2 := Iff.rfl

theorem sirkNS_diagMax_symmetricOn (c : ι → ℝ) : SymmetricOn (maxDom c) (diagMax c) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun k => ?_
  simp only [RCLike.inner_apply, diagMax_coe, map_mul, Complex.conj_ofReal]
  ring

theorem sirkNS_diagMax_hasSum_quadForm (c : ι → ℝ) (x : maxDom c) :
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

theorem sirkNS_diagMax_quadForm_nonneg (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (x : maxDom c) :
    0 ≤ quadForm (diagMax c) x := by
  refine (sirkNS_diagMax_hasSum_quadForm c x).nonneg fun k => ?_
  exact mul_nonneg (hc k) (sq_nonneg _)

theorem sirkNS_diagMax_quadForm_ge_norm_sq (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k) (x : maxDom c) :
    ‖(x : L2I ι)‖ ^ 2 ≤ quadForm (diagMax c) x := by
  have hnorm := lp.hasSum_norm (p := 2) (E := fun _ : ι => ℂ) (by norm_num) ((x : L2I ι))
  have h2 : ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2] at hnorm
  simp only [Real.rpow_natCast] at hnorm
  refine hasSum_le (fun k => ?_) hnorm (sirkNS_diagMax_hasSum_quadForm c x)
  nlinarith [sq_nonneg ‖((x : L2I ι) : ι → ℂ) k‖, hc k]

theorem sirkNS_diagMax_add_one_surjective (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (f : L2I ι) :
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
  have hgmem : Memℓp g 2 := sirkNS_memLpTwo_of_le f hgle
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
  refine ⟨⟨⟨g, hgmem⟩, sirkNS_memLpTwo_of_le f hcgle⟩, ?_⟩
  refine lp.ext (funext fun k => ?_)
  simp only [lp.coeFn_add, Pi.add_apply, diagMax_coe]
  change (c k : ℂ) * g k + g k = (f : ι → ℂ) k
  have : (c k : ℂ) * g k + g k = ((c k : ℂ) + 1) * g k := by ring
  rw [this, hg]
  simp only
  rw [mul_comm, div_mul_cancel₀ _ (hne k)]

theorem sirkNS_coe_sum_single [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) (k : ι) :
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

theorem sirkNS_sum_single_mem_finiteModes [DecidableEq ι] (S : Finset ι) (u : ι → ℂ) :
    (∑ i ∈ S, lp.single 2 i (u i) : L2I ι) ∈ lpFiniteModes ι :=
  Submodule.sum_mem _ fun i _ => lpSingle_mem_lpFiniteModes i (u i)

theorem sirkNS_exists_finiteModes_graph_approx (c : ι → ℝ) (x : maxDom c) (ε : ℝ) (hε : 0 < ε) :
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
    finiteModes_le_maxDom c (sirkNS_sum_single_mem_finiteModes S u)⟩,
    sirkNS_sum_single_mem_finiteModes S u, hS1, ?_⟩
  have hdiag : (diagMax c ⟨(∑ i ∈ S, lp.single 2 i (u i) : L2I ι),
      finiteModes_le_maxDom c (sirkNS_sum_single_mem_finiteModes S u)⟩ : L2I ι)
      = (∑ i ∈ S, lp.single 2 i (v i) : L2I ι) := by
    refine lp.ext (funext fun k => ?_)
    rw [diagMax_coe, sirkNS_coe_sum_single, sirkNS_coe_sum_single]
    by_cases hk : k ∈ S
    · simp [hk, hv, hu]
    · simp [hk]
  rw [hdiag]
  exact hS2

theorem sirkNS_commForm_self (c : ι → ℝ) (x : maxDom c) : commForm (diagMax c) (diagMax c) x = 0 := by
  rw [sirkNS_commForm_eq]
  have him : (inner ℂ (diagMax c x) (diagMax c x) : ℂ).im = 0 := by
    simpa using inner_self_im (𝕜 := ℂ) ((diagMax c x))
  rw [him]
  ring

theorem sirkNS_diagMax_essentiallySelfAdjointOn (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (maxDom c) (diagMax c) :=
  sirkNS_essentiallySelfAdjointOn_of_farisLavine (diagMax c) (diagMax c) 0
    (sirkNS_diagMax_symmetricOn c) (sirkNS_diagMax_symmetricOn c) le_rfl (sirkNS_diagMax_quadForm_nonneg c hc)
    (sirkNS_diagMax_add_one_surjective c hc)
    (fun x => by rw [sirkNS_commForm_self]; simp)

theorem sirkNS_ikebeKato_momentum (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((diagMax c).comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by
  refine sirkNS_essentiallySelfAdjointOn_core_of_farisLavine (finiteModes_le_maxDom c)
    (diagMax c) (diagMax c) 1 0 0 (sirkNS_diagMax_symmetricOn c) (sirkNS_diagMax_symmetricOn c) le_rfl
    (sirkNS_diagMax_quadForm_nonneg c hc) (sirkNS_diagMax_add_one_surjective c hc)
    (fun x => by rw [sirkNS_commForm_self]; simp)
    (fun x => by simp) ?_
  intro x ε hε
  obtain ⟨y, hy1, hy2, hy3⟩ := sirkNS_exists_finiteModes_graph_approx c x ε hε
  exact ⟨y, hy1, hy2, hy3⟩

theorem sirkNS_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
    (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H : maxDom c →ₗ[ℂ] L2I ι) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom c) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom c, ‖H x‖ ^ 2 ≤ a * ‖diagMax c x‖ ^ 2 + b * ‖(x : L2I ι)‖ ^ 2)
    (hcomm : ∀ x : maxDom c, |commForm H (diagMax c) x| ≤ cst * quadForm (diagMax c) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by
  refine sirkNS_essentiallySelfAdjointOn_core_of_farisLavine (finiteModes_le_maxDom c)
    H (diagMax c) a b cst hH (sirkNS_diagMax_symmetricOn c) hcst (sirkNS_diagMax_quadForm_nonneg c hc)
    (sirkNS_diagMax_add_one_surjective c hc) hcomm hrel ?_
  intro x ε hε
  obtain ⟨y, hy1, hy2, hy3⟩ := sirkNS_exists_finiteModes_graph_approx c x ε hε
  exact ⟨y, hy1, hy2, hy3⟩

end BookProof.NavierStokesFlow.IkebeKato
namespace BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow LpNat FarisLavine IkebeKato
variable {ι : Type*} (S : ShiftData ι)
theorem sirkNS_amp_le_symbol (β : ι) : S.amp β ≤ (1 / 4 + S.K) * S.sym β := by
  have h1 := S.amp_le β
  have h2 := S.sym_ge_one β
  nlinarith [S.K_nonneg]

theorem sirkNS_hop_mul (g : ι → ℂ) (Y : ι → ℂ) (β : ι) :
    S.hop g β * Y β = S.hop (fun α => g α * Y (S.shift α)) β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    rw [hop_shift, hop_shift]
  · rw [hop_eq_zero S g hb, hop_eq_zero S _ hb, zero_mul]

theorem sirkNS_mul_hop (g : ι → ℂ) (Y : ι → ℂ) (β : ι) :
    Y β * S.hop g β = S.hop (fun α => Y (S.shift α) * g α) β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    rw [hop_shift, hop_shift]
  · rw [hop_eq_zero S g hb, hop_eq_zero S _ hb, mul_zero]

theorem sirkNS_conj_hop (g : ι → ℂ) (β : ι) :
    (starRingEnd ℂ) (S.hop g β) = S.hop (fun α => (starRingEnd ℂ) (g α)) β := by
  by_cases hb : ∃ α, S.shift α = β
  · obtain ⟨α, rfl⟩ := hb
    rw [hop_shift, hop_shift]
  · rw [hop_eq_zero S g hb, hop_eq_zero S _ hb, map_zero]

theorem sirkNS_tsum_ampSeq_sq_le (x : maxDom S.sym) :
    (∑' β, (S.ampSeq ((x : L2I ι) : ι → ℂ) β) ^ 2)
      ≤ (1 / 8) * ‖(diagMax S.sym x : L2I ι)‖ ^ 2 + (2 * S.K ^ 2) * ‖(x : L2I ι)‖ ^ 2 := by
  refine le_trans (Summable.tsum_le_tsum (ampSeq_sq_le S x) (summable_ampSeq_sq S x)
    (hasSum_ampBound S x).summable) ?_
  exact le_of_eq (hasSum_ampBound S x).tsum_eq

theorem sirkNS_summable_ampOcc (x : maxDom S.sym) :
    Summable (fun β => S.amp β * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2) := by
  refine Summable.of_nonneg_of_le (fun β => mul_nonneg (S.amp_nonneg β) (sq_nonneg _))
    (fun β => ?_) ((sirkNS_diagMax_hasSum_quadForm S.sym x).summable.mul_left (1 / 4 + S.K))
  nlinarith [sirkNS_amp_le_symbol S β, sq_nonneg ‖((x : L2I ι) : ι → ℂ) β‖]

theorem sirkNS_tsum_ampOcc_le (x : maxDom S.sym) :
    (∑' β, S.amp β * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2)
      ≤ (1 / 4 + S.K) * quadForm (diagMax S.sym) x := by
  have hq := sirkNS_diagMax_hasSum_quadForm S.sym x
  refine le_trans (Summable.tsum_le_tsum (fun β => ?_) (sirkNS_summable_ampOcc S x)
    (hq.summable.mul_left (1 / 4 + S.K))) ?_
  · nlinarith [sirkNS_amp_le_symbol S β, sq_nonneg ‖((x : L2I ι) : ι → ℂ) β‖]
  · exact le_of_eq (hq.mul_left (1 / 4 + S.K)).tsum_eq

theorem sirkNS_abs_le_of_hasSum {f g : ι → ℝ} {A B : ℝ} (hf : HasSum f A) (hg : HasSum g B)
    (h : ∀ β, |f β| ≤ g β) : |A| ≤ B := by
  refine abs_le.mpr ⟨?_, hasSum_le (fun β => le_trans (le_abs_self _) (h β)) hf hg⟩
  have hneg : HasSum (fun β => -g β) (-B) := hg.neg
  have := hasSum_le (fun β => by linarith [neg_abs_le (f β), h β] : ∀ β, -g β ≤ f β) hneg hf
  linarith

end BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
namespace BookProof.NavierStokesFlow.AffineFiber
open BookProof.NavierStokesFlow LpNat FarisLavine IkebeKato
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
theorem sirkNS_commForm_add (H₁ H₂ N : D →ₗ[ℂ] F) (x : D) :
    commForm (H₁ + H₂) N x = commForm H₁ N x + commForm H₂ N x := by
  simp only [commForm, LinearMap.add_apply, inner_add_left, inner_add_right]
  have : Complex.I * (inner ℂ (H₁ x) (N x) + inner ℂ (H₂ x) (N x)
      - (inner ℂ (N x) (H₁ x) + inner ℂ (N x) (H₂ x)))
      = Complex.I * (inner ℂ (H₁ x) (N x) - inner ℂ (N x) (H₁ x))
        + Complex.I * (inner ℂ (H₂ x) (N x) - inner ℂ (N x) (H₂ x)) := by ring
  rw [this, Complex.add_re]

end BookProof.NavierStokesFlow.AffineFiber

namespace BookProof.NavierStokesFlow
namespace SignedShift
open LpNat FarisLavine IkebeKato ShiftHamiltonian AffineFiber
open scoped ENNReal
variable {ι : Type*}
namespace SignedHop
variable {sym : ι → ℝ} (S : SignedHop ι sym)
@[simp] theorem sirkNS_maj_sym : S.maj.sym = sym := rfl

@[simp] theorem sirkNS_maj_shift : S.maj.shift = S.shift := rfl

@[simp] theorem sirkNS_maj_amp : S.maj.amp = S.bnd := rfl

@[simp] theorem sirkNS_maj_K : S.maj.K = S.K := rfl

@[simp] theorem sirkNS_maj_step : S.maj.step = S.step := rfl

@[simp] theorem sirkNS_hopH_coe (x : maxDom sym) (β : ι) :
    ((hopH S x : L2I ι) : ι → ℂ) β = S.hFun ((x : L2I ι) : ι → ℂ) β := rfl

theorem sirkNS_norm_crossA_le (X Y : ι → ℂ) (β : ι) :
    ‖S.crossA X Y β‖ ≤ S.maj.ampSeq X β * ‖Y (S.shift β)‖ := by
  simp only [crossA, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
  have h : |S.amp β| * ‖X β‖ ≤ S.bnd β * ‖X β‖ :=
    mul_le_mul_of_nonneg_right (S.abs_amp_le_bnd β) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

theorem sirkNS_norm_crossB_le (X Y : ι → ℂ) (β : ι) :
    ‖S.crossB X Y β‖ ≤ S.maj.ampSeq X (S.shift β) * ‖Y β‖ := by
  simp only [crossB, norm_mul, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj]
  have h1 : |S.amp β| * ‖X (S.shift β)‖ ≤ S.bnd (S.shift β) * ‖X (S.shift β)‖ :=
    mul_le_mul_of_nonneg_right (le_trans (S.abs_amp_le_bnd β) (S.bnd_mono β)) (norm_nonneg _)
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

theorem sirkNS_summable_crossA {X Y : ι → ℂ}
    (hX : Summable fun β => (S.maj.ampSeq X β) ^ 2) (hY : Summable fun β => ‖Y β‖ ^ 2) :
    Summable (S.crossA X Y) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun β => norm_nonneg _) (fun β => ?_)
    ((hX.add (ShiftData.summable_comp_shift S.maj hY)).mul_left (1 / 2)))
  have h := sirkNS_norm_crossA_le S X Y β
  simp only [sirkNS_maj_shift]
  nlinarith [sq_nonneg (S.maj.ampSeq X β - ‖Y (S.shift β)‖),
    ShiftData.ampSeq_nonneg S.maj X β, norm_nonneg (Y (S.shift β)), h]

theorem sirkNS_summable_crossB {X Y : ι → ℂ}
    (hX : Summable fun β => (S.maj.ampSeq X β) ^ 2) (hY : Summable fun β => ‖Y β‖ ^ 2) :
    Summable (S.crossB X Y) := by
  refine Summable.of_norm (Summable.of_nonneg_of_le (fun β => norm_nonneg _) (fun β => ?_)
    (((ShiftData.summable_comp_shift S.maj hX).add hY).mul_left (1 / 2)))
  have h := sirkNS_norm_crossB_le S X Y β
  simp only [sirkNS_maj_shift]
  nlinarith [sq_nonneg (S.maj.ampSeq X (S.shift β) - ‖Y β‖),
    ShiftData.ampSeq_nonneg S.maj X (S.shift β), norm_nonneg (Y β), h]

theorem sirkNS_conj_hFun_mul (X Y : ι → ℂ) (β : ι) :
    (starRingEnd ℂ) (S.hFun X β) * Y β
      = -Complex.I * S.maj.hop (S.crossA X Y) β + Complex.I * S.crossB X Y β := by
  have h1 : (starRingEnd ℂ) (S.maj.hop (fun α => (S.amp α : ℂ) * X α) β)
      = S.maj.hop (fun α => (S.amp α : ℂ) * (starRingEnd ℂ) (X α)) β := by
    rw [ShiftData.sirkNS_conj_hop]
    congr 1
    funext α
    simp
  have h2 : S.maj.hop (fun α => (S.amp α : ℂ) * (starRingEnd ℂ) (X α)) β * Y β
      = S.maj.hop (S.crossA X Y) β := by
    rw [ShiftData.sirkNS_hop_mul]
    rfl
  have hexp : (starRingEnd ℂ) (S.hFun X β) * Y β
      = -Complex.I * ((starRingEnd ℂ) (S.maj.hop (fun α => (S.amp α : ℂ) * X α) β) * Y β)
        + Complex.I * ((S.amp β : ℂ) * (starRingEnd ℂ) (X (S.shift β)) * Y β) := by
    simp only [hFun, map_mul, map_sub, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hexp, h1, h2]
  rfl

theorem sirkNS_conj_mul_hFun (X Y : ι → ℂ) (β : ι) :
    (starRingEnd ℂ) (X β) * S.hFun Y β
      = -Complex.I * S.crossA X Y β + Complex.I * S.maj.hop (S.crossB X Y) β := by
  have h2 : (starRingEnd ℂ) (X β) * S.maj.hop (fun α => (S.amp α : ℂ) * Y α) β
      = S.maj.hop (S.crossB X Y) β := by
    by_cases hb : ∃ α, S.maj.shift α = β
    · obtain ⟨α, rfl⟩ := hb
      rw [ShiftData.hop_shift, ShiftData.hop_shift]
      simp only [crossB, sirkNS_maj_shift]
      ring
    · rw [ShiftData.hop_eq_zero _ _ hb, ShiftData.hop_eq_zero _ _ hb, mul_zero]
  have hexp : (starRingEnd ℂ) (X β) * S.hFun Y β
      = Complex.I * ((starRingEnd ℂ) (X β) * S.maj.hop (fun α => (S.amp α : ℂ) * Y α) β)
        - Complex.I * ((S.amp β : ℂ) * (starRingEnd ℂ) (X β) * Y (S.shift β)) := by
    simp only [hFun]
    ring
  rw [hexp, h2]
  simp only [crossA]
  ring

theorem sirkNS_hasSum_inner_hopH_left (x : maxDom sym) (y : L2I ι) :
    HasSum (fun β => -Complex.I * S.crossA ((x : L2I ι) : ι → ℂ) ((y : ι → ℂ)) β
        + Complex.I * S.crossB ((x : L2I ι) : ι → ℂ) ((y : ι → ℂ)) β)
      (inner ℂ (hopH S x : L2I ι) y) := by
  have hA := sirkNS_summable_crossA S (Y := (y : ι → ℂ)) (ShiftData.summable_ampSeq_sq S.maj x)
    (sirkNS_summable_normSq y)
  have hB := sirkNS_summable_crossB S (Y := (y : ι → ℂ)) (ShiftData.summable_ampSeq_sq S.maj x)
    (sirkNS_summable_normSq y)
  have hgoal := (hA.hasSum.mul_left (-Complex.I)).add (hB.hasSum.mul_left Complex.I)
  have hshift := (((ShiftData.hasSum_hop_iff S.maj).mpr hA.hasSum).mul_left (-Complex.I)).add
    (hB.hasSum.mul_left Complex.I)
  have hinner := lp.hasSum_inner (𝕜 := ℂ) ((hopH S x : L2I ι)) y
  have heq : (fun β => (inner ℂ (((hopH S x : L2I ι) : ι → ℂ) β) ((y : ι → ℂ) β) : ℂ))
      = fun β => -Complex.I * S.maj.hop (S.crossA ((x : L2I ι) : ι → ℂ) ((y : ι → ℂ))) β
          + Complex.I * S.crossB ((x : L2I ι) : ι → ℂ) ((y : ι → ℂ)) β := by
    funext β
    rw [RCLike.inner_apply, sirkNS_hopH_coe, mul_comm]
    exact sirkNS_conj_hFun_mul S _ _ β
  rw [heq] at hinner
  rwa [hshift.unique hinner] at hgoal

theorem sirkNS_hasSum_inner_hopH_right (x y : maxDom sym) :
    HasSum (fun β => -Complex.I * S.crossA ((x : L2I ι) : ι → ℂ) (((y : L2I ι) : ι → ℂ)) β
        + Complex.I * S.crossB ((x : L2I ι) : ι → ℂ) (((y : L2I ι) : ι → ℂ)) β)
      (inner ℂ (x : L2I ι) (hopH S y : L2I ι)) := by
  have hA := sirkNS_summable_crossA S (Y := ((y : L2I ι) : ι → ℂ))
    (ShiftData.summable_ampSeq_sq S.maj x) (sirkNS_summable_normSq (y : L2I ι))
  have hB := sirkNS_summable_crossB S (Y := ((y : L2I ι) : ι → ℂ))
    (ShiftData.summable_ampSeq_sq S.maj x) (sirkNS_summable_normSq (y : L2I ι))
  have hgoal := (hA.hasSum.mul_left (-Complex.I)).add (hB.hasSum.mul_left Complex.I)
  have hshift := (hA.hasSum.mul_left (-Complex.I)).add
    (((ShiftData.hasSum_hop_iff S.maj).mpr hB.hasSum).mul_left Complex.I)
  have hinner := lp.hasSum_inner (𝕜 := ℂ) ((x : L2I ι)) ((hopH S y : L2I ι))
  have heq : (fun β => (inner ℂ (((x : L2I ι) : ι → ℂ) β)
        (((hopH S y : L2I ι) : ι → ℂ) β) : ℂ))
      = fun β => -Complex.I * S.crossA ((x : L2I ι) : ι → ℂ) (((y : L2I ι) : ι → ℂ)) β
          + Complex.I * S.maj.hop (S.crossB ((x : L2I ι) : ι → ℂ)
            (((y : L2I ι) : ι → ℂ))) β := by
    funext β
    rw [RCLike.inner_apply, sirkNS_hopH_coe, mul_comm]
    exact sirkNS_conj_mul_hFun S _ _ β
  rw [heq] at hinner
  rwa [hshift.unique hinner] at hgoal

theorem sirkNS_hopH_symmetricOn : SymmetricOn (maxDom sym) (hopH S) := by
  intro x y
  exact (sirkNS_hasSum_inner_hopH_left S x (y : L2I ι)).unique (sirkNS_hasSum_inner_hopH_right S x y)

theorem sirkNS_hopH_relative_bound (x : maxDom sym) :
    ‖(hopH S x : L2I ι)‖ ^ 2
      ≤ (1 / 2) * ‖(diagMax sym x : L2I ι)‖ ^ 2 + (8 * S.K ^ 2) * ‖(x : L2I ι)‖ ^ 2 := by
  have hS := ShiftData.summable_ampSeq_sq S.maj x
  have hshift : Summable (S.maj.hop fun β => (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) β) ^ 2) :=
    ShiftData.summable_hop S.maj hS
  have htail : Summable (fun β => (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) (S.maj.shift β)) ^ 2) :=
    ShiftData.summable_comp_shift S.maj hS
  have hbound := (hshift.hasSum.mul_left 2).add (htail.hasSum.mul_left 2)
  have hle : ‖(hopH S x : L2I ι)‖ ^ 2
      ≤ 2 * (∑' β, S.maj.hop (fun α => (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) α) ^ 2) β)
        + 2 * ∑' β, (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) (S.maj.shift β)) ^ 2 := by
    refine hasSum_le (fun β => ?_) (ShiftData.hasSum_normSq (hopH S x : L2I ι)) hbound
    rw [sirkNS_hopH_coe]
    exact normSq_hFun_le S _ β
  have hshifteq : (∑' β, S.maj.hop (fun α => (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) α) ^ 2) β)
      = ∑' β, (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) β) ^ 2 :=
    ((ShiftData.hasSum_hop_iff S.maj).mpr hS.hasSum).tsum_eq
  have htaille : (∑' β, (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) (S.maj.shift β)) ^ 2)
      ≤ ∑' β, (S.maj.ampSeq ((x : L2I ι) : ι → ℂ) β) ^ 2 :=
    tsum_comp_le_tsum_of_inj hS (fun _ => sq_nonneg _) S.maj.shift_injective
  have hT := ShiftData.sirkNS_tsum_ampSeq_sq_le S.maj x
  rw [hshifteq] at hle
  have hdiag : (diagMax S.maj.sym x : L2I ι) = (diagMax sym x : L2I ι) := rfl
  rw [hdiag] at hT
  have hK : S.maj.K = S.K := rfl
  rw [hK] at hT
  linarith

theorem sirkNS_hasSum_commForm (x : maxDom sym) :
    HasSum (fun β => 2 * S.step * (S.amp β
        * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
            * ((x : L2I ι) : ι → ℂ) (S.shift β)).re))
      (commForm (hopH S) (diagMax sym) x) := by
  have hL := sirkNS_hasSum_inner_hopH_left S x (diagMax sym x : L2I ι)
  have hIm := Complex.hasSum_im hL
  have hpt : ∀ β, (-Complex.I * S.crossA ((x : L2I ι) : ι → ℂ)
        (((diagMax sym x : L2I ι) : ι → ℂ)) β
      + Complex.I * S.crossB ((x : L2I ι) : ι → ℂ)
        (((diagMax sym x : L2I ι) : ι → ℂ)) β).im
      = -S.step * (S.amp β * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
        * ((x : L2I ι) : ι → ℂ) (S.shift β)).re) := by
    intro β
    simp only [crossA, crossB, diagMax_coe, S.sym_step]
    simp [Complex.add_im, Complex.mul_im, Complex.mul_re]
    ring
  have hIm' : HasSum (fun β => -S.step * (S.amp β
      * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
        * ((x : L2I ι) : ι → ℂ) (S.shift β)).re))
      (inner ℂ (hopH S x : L2I ι) (diagMax sym x : L2I ι) : ℂ).im := by
    refine hIm.congr_fun ?_
    intro β
    exact (hpt β).symm
  have hres := hIm'.mul_left (-2)
  rw [sirkNS_commForm_eq]
  refine hres.congr_fun ?_
  intro β
  ring

theorem sirkNS_hopH_commForm_bound (x : maxDom sym) :
    |commForm (hopH S) (diagMax sym) x|
      ≤ (2 * S.step * (1 / 4 + S.K)) * quadForm (diagMax sym) x := by
  have hus := ShiftData.sirkNS_summable_ampOcc S.maj x
  have hutail : Summable (fun β => S.maj.amp (S.maj.shift β)
      * ‖((x : L2I ι) : ι → ℂ) (S.maj.shift β)‖ ^ 2) :=
    ShiftData.summable_comp_shift S.maj hus
  have hbound : HasSum (fun β => S.step * (S.bnd β * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2
      + S.bnd (S.shift β) * ‖((x : L2I ι) : ι → ℂ) (S.shift β)‖ ^ 2))
      (S.step * ((∑' β, S.maj.amp β * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2)
        + ∑' β, S.maj.amp (S.maj.shift β)
          * ‖((x : L2I ι) : ι → ℂ) (S.maj.shift β)‖ ^ 2)) :=
    (hus.hasSum.add hutail.hasSum).mul_left S.step
  have hptle : ∀ β, |2 * S.step * (S.amp β * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
        * ((x : L2I ι) : ι → ℂ) (S.shift β)).re)|
      ≤ S.step * (S.bnd β * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2
        + S.bnd (S.shift β) * ‖((x : L2I ι) : ι → ℂ) (S.shift β)‖ ^ 2) := by
    intro β
    have hstep : 0 ≤ S.step := S.step_nonneg
    have habs : 0 ≤ |S.amp β| := abs_nonneg _
    have hre : |((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
        * ((x : L2I ι) : ι → ℂ) (S.shift β)).re|
        ≤ ‖((x : L2I ι) : ι → ℂ) β‖ * ‖((x : L2I ι) : ι → ℂ) (S.shift β)‖ := by
      refine le_trans (Complex.abs_re_le_norm _) ?_
      rw [norm_mul, RCLike.norm_conj]
    set R := ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) β)
      * ((x : L2I ι) : ι → ℂ) (S.shift β)).re with hR
    set u := ‖((x : L2I ι) : ι → ℂ) β‖ with hu
    set v := ‖((x : L2I ι) : ι → ℂ) (S.shift β)‖ with hv
    have hu0 : 0 ≤ u := norm_nonneg _
    have hv0 : 0 ≤ v := norm_nonneg _
    have hrw : |2 * S.step * (S.amp β * R)| = 2 * S.step * (|S.amp β| * |R|) := by
      rw [show (2 : ℝ) * S.step * (S.amp β * R) = (2 * S.step) * (S.amp β * R) from by ring,
        abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * S.step), abs_mul]
    have hA : 2 * S.step * (|S.amp β| * |R|) ≤ 2 * S.step * (|S.amp β| * (u * v)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hre habs) (by positivity)
    have h2ab : 2 * (u * v) ≤ u ^ 2 + v ^ 2 := by nlinarith [sq_nonneg (u - v)]
    have hB : 2 * S.step * (|S.amp β| * (u * v))
        ≤ S.step * (|S.amp β| * u ^ 2 + |S.amp β| * v ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left h2ab
        (show (0 : ℝ) ≤ S.step * |S.amp β| by positivity)]
    have hb1 : |S.amp β| * u ^ 2 ≤ S.bnd β * u ^ 2 :=
      mul_le_mul_of_nonneg_right (S.abs_amp_le_bnd β) (sq_nonneg _)
    have hb2 : |S.amp β| * v ^ 2 ≤ S.bnd (S.shift β) * v ^ 2 :=
      mul_le_mul_of_nonneg_right (le_trans (S.abs_amp_le_bnd β) (S.bnd_mono β)) (sq_nonneg _)
    have hC : S.step * (|S.amp β| * u ^ 2 + |S.amp β| * v ^ 2)
        ≤ S.step * (S.bnd β * u ^ 2 + S.bnd (S.shift β) * v ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hstep
    rw [hrw]
    linarith [hA, hB, hC]
  have habs := ShiftData.sirkNS_abs_le_of_hasSum (sirkNS_hasSum_commForm S x) hbound hptle
  have htail : (∑' β, S.maj.amp (S.maj.shift β)
        * ‖((x : L2I ι) : ι → ℂ) (S.maj.shift β)‖ ^ 2)
      ≤ ∑' β, S.maj.amp β * ‖((x : L2I ι) : ι → ℂ) β‖ ^ 2 :=
    tsum_comp_le_tsum_of_inj hus
      (fun β => mul_nonneg (S.maj.amp_nonneg β) (sq_nonneg _)) S.maj.shift_injective
  have hU := ShiftData.sirkNS_tsum_ampOcc_le S.maj x
  have hdiag : quadForm (diagMax S.maj.sym) x = quadForm (diagMax sym) x := rfl
  rw [hdiag] at hU
  have hK : S.maj.K = S.K := rfl
  rw [hK] at hU
  have hqf : 0 ≤ quadForm (diagMax sym) x :=
    sirkNS_diagMax_quadForm_nonneg _ (fun β => le_trans zero_le_one (S.sym_ge_one β)) x
  refine le_trans habs ?_
  nlinarith [hU, htail, S.step_nonneg, S.K_nonneg]


end SignedHop
variable {sym : ι → ℝ}
@[simp] theorem sirkNS_listH_nil : listH ([] : List (SignedHop ι sym)) = 0 := rfl

@[simp] theorem sirkNS_listH_cons (S : SignedHop ι sym) (L : List (SignedHop ι sym)) :
    listH (S :: L) = SignedHop.hopH S + listH L := rfl

theorem sirkNS_listH_symmetricOn (L : List (SignedHop ι sym)) : SymmetricOn (maxDom sym) (listH L) := by
  induction L with
  | nil =>
      intro x y
      simp [listH]
  | cons S L ih =>
      intro x y
      have h₁ := SignedHop.sirkNS_hopH_symmetricOn S x y
      have h₂ := ih x y
      change (inner ℂ (listH (S :: L) x : L2I ι) (y : L2I ι) : ℂ)
        = inner ℂ (x : L2I ι) (listH (S :: L) y : L2I ι)
      simp only [sirkNS_listH_cons, LinearMap.add_apply, inner_add_left, inner_add_right]
      linear_combination h₁ + h₂

theorem sirkNS_listH_relative_bound (L : List (SignedHop ι sym)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ x : maxDom sym,
      ‖(listH L x : L2I ι)‖ ^ 2
        ≤ a * ‖(diagMax sym x : L2I ι)‖ ^ 2 + b * ‖(x : L2I ι)‖ ^ 2 := by
  induction L with
  | nil =>
      refine ⟨0, 0, le_rfl, le_rfl, fun x => ?_⟩
      simp [listH]
  | cons S L ih =>
      obtain ⟨a, b, ha, hb, hbound⟩ := ih
      refine ⟨2 * (1 / 2) + 2 * a, 2 * (8 * S.K ^ 2) + 2 * b, by linarith,
        by nlinarith [sq_nonneg S.K], fun x => ?_⟩
      have h₁ := SignedHop.sirkNS_hopH_relative_bound S x
      have h₂ := hbound x
      have htri : ‖(listH (S :: L) x : L2I ι)‖
          ≤ ‖(SignedHop.hopH S x : L2I ι)‖ + ‖(listH L x : L2I ι)‖ := by
        simp only [sirkNS_listH_cons, LinearMap.add_apply]
        exact norm_add_le _ _
      have hsq : ‖(listH (S :: L) x : L2I ι)‖ ^ 2
          ≤ 2 * ‖(SignedHop.hopH S x : L2I ι)‖ ^ 2 + 2 * ‖(listH L x : L2I ι)‖ ^ 2 := by
        nlinarith [norm_nonneg (listH (S :: L) x : L2I ι),
          norm_nonneg (SignedHop.hopH S x : L2I ι), norm_nonneg (listH L x : L2I ι),
          sq_nonneg (‖(SignedHop.hopH S x : L2I ι)‖ - ‖(listH L x : L2I ι)‖)]
      nlinarith [h₁, h₂, hsq]

theorem sirkNS_listH_commForm_bound (L : List (SignedHop ι sym)) (hsym : ∀ β, 1 ≤ sym β) :
    ∃ cst : ℝ, 0 ≤ cst ∧ ∀ x : maxDom sym,
      |commForm (listH L) (diagMax sym) x| ≤ cst * quadForm (diagMax sym) x := by
  induction L with
  | nil =>
      refine ⟨0, le_rfl, fun x => ?_⟩
      have : commForm (listH ([] : List (SignedHop ι sym))) (diagMax sym) x = 0 := by
        simp [commForm, listH]
      rw [this]
      simp
  | cons S L ih =>
      obtain ⟨cst, hcst, hbound⟩ := ih
      refine ⟨2 * S.step * (1 / 4 + S.K) + cst, by nlinarith [S.step_nonneg, S.K_nonneg],
        fun x => ?_⟩
      have h₁ := SignedHop.sirkNS_hopH_commForm_bound S x
      have h₂ := hbound x
      have hadd : commForm (listH (S :: L)) (diagMax sym) x
          = commForm (SignedHop.hopH S) (diagMax sym) x + commForm (listH L) (diagMax sym) x := by
        simpa only [sirkNS_listH_cons] using sirkNS_commForm_add (SignedHop.hopH S) (listH L) (diagMax sym) x
      have hqf : 0 ≤ quadForm (diagMax sym) x :=
        sirkNS_diagMax_quadForm_nonneg _ (fun β => le_trans zero_le_one (hsym β)) x
      rw [hadd]
      refine le_trans (abs_add_le _ _) ?_
      nlinarith [h₁, h₂]

theorem SignedHop.sirkNS_hFun_single [DecidableEq ι] {sym : ι → ℝ} (S : SignedHop ι sym)
    {X : ι → ℂ} {o : ι} (hX : ∀ α, X α = if α = o then 1 else 0) (γ : ι) :
    S.hFun X γ = Complex.I * ((if γ = S.shift o then (S.amp o : ℂ) else 0)
      - (if S.shift γ = o then (S.amp γ : ℂ) else 0)) := by
  have h2 : (S.amp γ : ℂ) * X (S.shift γ)
      = if S.shift γ = o then (S.amp γ : ℂ) else 0 := by
    rw [hX]
    split <;> simp
  have h1 : S.maj.hop (fun α => (S.amp α : ℂ) * X α) γ
      = if γ = S.shift o then (S.amp o : ℂ) else 0 := by
    by_cases hb : ∃ α, S.shift α = γ
    · obtain ⟨α, rfl⟩ := hb
      have hiff : S.shift α = S.shift o ↔ α = o :=
        ⟨fun h => S.shift_injective h, fun h => by rw [h]⟩
      rw [show S.shift α = S.maj.shift α from rfl, ShiftData.hop_shift, hX]
      by_cases hao : α = o
      · subst hao; simp
      · rw [if_neg hao, mul_zero]
        exact (if_neg (fun h => hao (hiff.mp h))).symm
    · rw [ShiftData.hop_eq_zero _ _ (by simpa using hb)]
      exact (if_neg (fun h => hb ⟨o, h.symm⟩)).symm
  rw [SignedHop.hFun, h1, h2]

theorem sirkNS_listH_coe {sym : ι → ℝ} (L : List (SignedHop ι sym)) (x : maxDom sym) (γ : ι) :
    ((listH L x : L2I ι) : ι → ℂ) γ
      = (L.map (fun S => S.hFun ((x : L2I ι) : ι → ℂ) γ)).sum := by
  induction L with
  | nil => simp [listH]
  | cons S L ih =>
      rw [sirkNS_listH_cons]
      simp only [LinearMap.add_apply, lp.coeFn_add, Pi.add_apply, List.map_cons,
        List.sum_cons, SignedHop.sirkNS_hopH_coe, ih]


section GeneralAffine
variable (kap cst : ℝ)
theorem sirkNS_gaffH_symmetricOn : SymmetricOn (maxDom (gsym kap cst)) (gaffH kap cst) :=
  sirkNS_listH_symmetricOn _

end GeneralAffine
end SignedShift
end BookProof.NavierStokesFlow

namespace BookProof.NavierStokesFlow.SignedShift
open BookProof.NavierStokesFlow LpNat FarisLavine IkebeKato ShiftHamiltonian AffineFiber
variable {ι : Type*}
namespace SignedHop
variable {sym : ι → ℝ} (S : SignedHop ι sym)
theorem sirkNS_hopH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((hopH S).comp (Submodule.inclusion (finiteModes_le_maxDom sym))) :=
  sirkNS_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds sym
    (fun β => le_trans zero_le_one (S.sym_ge_one β))
    (hopH S) (1 / 2) (8 * S.K ^ 2) (2 * S.step * (1 / 4 + S.K))
    (sirkNS_hopH_symmetricOn S) (by nlinarith [S.step_nonneg, S.K_nonneg])
    (sirkNS_hopH_relative_bound S) (sirkNS_hopH_commForm_bound S)
end SignedHop
variable {sym : ι → ℝ}
theorem sirkNS_listH_essentiallySelfAdjointOn_core (L : List (SignedHop ι sym)) (hsym : ∀ β, 1 ≤ sym β) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((listH L).comp (Submodule.inclusion (finiteModes_le_maxDom sym))) := by
  obtain ⟨a, b, _, _, hrel⟩ := sirkNS_listH_relative_bound L
  obtain ⟨cst, hcst, hcomm⟩ := sirkNS_listH_commForm_bound L hsym
  exact sirkNS_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds sym
    (fun β => le_trans zero_le_one (hsym β)) (listH L) a b cst
    (sirkNS_listH_symmetricOn L) hcst hrel hcomm
variable (kap cst : ℝ)
theorem sirkNS_gaffH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      ((gaffH kap cst).comp (Submodule.inclusion (finiteModes_le_maxDom (gsym kap cst)))) :=
  sirkNS_listH_essentiallySelfAdjointOn_core _ (gsym_ge_one kap cst)
end BookProof.NavierStokesFlow.SignedShift
namespace BookProof.HashimotoShiftInvert
open BookProof.FarisLavine
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] {Dom : Submodule ℂ F}
private theorem IsShiftInvertC.mem {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) : X u ∈ Dom := (h.2 u).choose

private theorem IsShiftInvertC.shift_apply {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (u : F) :
    γ • X u - A ⟨X u, h.mem u⟩ = u := (h.2 u).choose_spec

private theorem IsShiftInvertC.norm_apply_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) (u : F) :
    ‖X u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hb : |γ.im| * ‖((⟨X u, h.mem u⟩ : Dom) : F)‖ ≤ ‖cshiftMap A γ ⟨X u, h.mem u⟩‖ :=
    norm_cshiftMap_ge hsym _ _
  rw [show cshiftMap A γ ⟨X u, h.mem u⟩ = u from h.shift_apply u] at hb
  rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
  simpa using hb

private theorem IsShiftInvertC.opNorm_le {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (h : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) :
    ‖X‖ ≤ |γ.im|⁻¹ :=
  X.opNorm_le_bound (by positivity) (h.norm_apply_le hsym hγ)

private theorem exists_isShiftInvertC {A : Dom →ₗ[ℂ] F} (hsym : SymmetricOn Dom A)
    {γ : ℂ} (hγ : γ.im ≠ 0) (hsurj : Function.Surjective (cshiftMap A γ)) :
    ∃ X : F →L[ℂ] F, IsShiftInvertC A γ X := by
  classical
  have hpos : 0 < |γ.im| := abs_pos.mpr hγ
  have hinj : Function.Injective (cshiftMap A γ) := cshiftMap_injective hsym hγ
  choose g hg using hsurj
  have hgshift : ∀ x : Dom, g (cshiftMap A γ x) = x := fun x => hinj (hg _)
  have hadd : ∀ u v : F, ((g (u + v) : Dom) : F) = (g u : F) + (g v : F) := by
    intro u v
    have : cshiftMap A γ (g (u + v)) = cshiftMap A γ (g u + g v) := by
      rw [hg, map_add, hg, hg]
    exact congrArg Subtype.val (hinj this)
  have hsmul : ∀ (c : ℂ) (u : F), ((g (c • u) : Dom) : F) = c • (g u : F) := by
    intro c u
    have : cshiftMap A γ (g (c • u)) = cshiftMap A γ (c • g u) := by
      rw [hg, map_smul, hg]
    exact congrArg Subtype.val (hinj this)
  let L : F →ₗ[ℂ] F :=
    { toFun := fun u => (g u : F)
      map_add' := hadd
      map_smul' := by intro c u; simpa using hsmul c u }
  have hbound : ∀ u : F, ‖L u‖ ≤ |γ.im|⁻¹ * ‖u‖ := by
    intro u
    have hb : |γ.im| * ‖((g u : Dom) : F)‖ ≤ ‖cshiftMap A γ (g u)‖ := norm_cshiftMap_ge hsym _ _
    rw [hg u] at hb
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact hb
  refine ⟨L.mkContinuous |γ.im|⁻¹ hbound, fun x => ?_, fun u => ?_⟩
  · change ((g (cshiftMap A γ x) : Dom) : F) = (x : F)
    rw [hgshift x]
  · refine ⟨(g u).2, ?_⟩
    have hsub : (⟨((g u : Dom) : F), (g u).2⟩ : Dom) = g u := Subtype.ext rfl
    change cshiftMap A γ ⟨((g u : Dom) : F), _⟩ = u
    rw [hsub, hg u]

end BookProof.HashimotoShiftInvert
namespace SirkComplexGeometryAux
open BookProof.ChapterH4 BookProof.ChapterH9 BookProof.HashimotoShiftInvert BookProof.FarisLavine
variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] {Dom : Submodule ℂ F}
private theorem krylov_rayleigh_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E) (y : F) :
    inner ℂ y (compress V X y) = inner ℂ (V y) (X (V y)) := by
  rw [compress]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_right V y (X (V y))

private theorem numRange_compress_subset (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) : numRange (compress V X) ⊆ numRange X := by
  rintro c ⟨y, hy, rfl⟩
  exact ⟨V y, by rw [hViso, hy], (krylov_rayleigh_transfer V X y).symm⟩

private theorem numRange_subset_closedBall (X : E →L[ℂ] E) :
    numRange X ⊆ Metric.closedBall (0 : ℂ) ‖X‖ := by
  rintro c ⟨x, hx, rfl⟩
  have hcs : ‖(inner ℂ x (X x) : ℂ)‖ ≤ ‖x‖ * ‖X x‖ := norm_inner_le_norm _ _
  have hXb : ‖X x‖ ≤ ‖X‖ := by simpa [hx] using X.le_opNorm x
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖(inner ℂ x (X x) : ℂ)‖ ≤ ‖x‖ * ‖X x‖ := hcs
    _ = ‖X x‖ := by rw [hx, one_mul]
    _ ≤ ‖X‖ := hXb

private theorem crouzeix_domain_transfer (V : F →L[ℂ] E) (X : E →L[ℂ] E)
    (hViso : ∀ x : F, ‖V x‖ = ‖x‖) (S : Set ℂ) (hconv : Convex ℝ S)
    (hS : numRange X ⊆ S) :
    (convexHull ℝ) (numRange (compress V X)) ⊆ S :=
  convexHull_min ((numRange_compress_subset V X hViso).trans hS) hconv

private theorem numRange_subset_closedBall_of_shiftInvertC {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0) :
    numRange X ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ :=
  (numRange_subset_closedBall X).trans
    (Metric.closedBall_subset_closedBall (hX.opNorm_le hsym hγ))

private theorem crouzeix_domain_shiftInvertC {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G] {A : Dom →ₗ[ℂ] F} {γ : ℂ} {X : F →L[ℂ] F}
    (hX : IsShiftInvertC A γ X) (hsym : SymmetricOn Dom A) (hγ : γ.im ≠ 0)
    (V : G →L[ℂ] F) (hViso : ∀ x : G, ‖V x‖ = ‖x‖) :
    convexHull ℝ (numRange (compress V X)) ⊆ Metric.closedBall (0 : ℂ) |γ.im|⁻¹ :=
  crouzeix_domain_transfer V X hViso _ (convex_closedBall _ _)
    (numRange_subset_closedBall_of_shiftInvertC hX hsym hγ)

end SirkComplexGeometryAux

-- Generated from ChapterSirkPerSystem.lean — theorem BookProof.ChapterSirkPerSystem.ns_sirk_crouzeix_domain
open BookProof.ChapterSirkPerSystem









noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH9 BookProof.ChapterSirkSpectralGeometry
open BookProof.HashimotoShiftInvert BookProof.FarisLavine BookProof.EsaClosure
open BookProof.YangMillsFriedrichs BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.Starobinsky
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.NSHashimoto
open BookProof.NavierStokesFlow.DiffHashimoto BookProof.NavierStokesFlow.DifferentialL2
open BookProof.NavierStokesFlow.LagrangianEsa BookProof.NavierStokesFlow.LagrangianKatoRellich
theorem solution (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)
    (b : HilbertBasis ℕ ℂ (L2I Vel)) (γ : ℕ → ℂ) (hγ : ∀ j, (γ j).im ≠ 0) :
    ∃ (Dom : Submodule ℂ (L2I Vel)) (G : Dom →ₗ[ℂ] L2I Vel)
      (X : ℕ → L2I Vel →L[ℂ] L2I Vel),
      IsSelfAdjointExtension (velCore A c) G ∧
      (∀ j, IsShiftInvertC G (γ j) (X j)) ∧
      (∀ j, numRange (X j) ⊆ Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹) ∧
      ∀ (j m : ℕ) (V : EuclideanSpace ℂ (Fin m) →L[ℂ] L2I Vel), (∀ x, ‖V x‖ = ‖x‖) →
        convexHull ℝ (numRange (compress V (X j)))
          ⊆ Metric.closedBall (0 : ℂ) |(γ j).im|⁻¹ := by
  have hsym : SymmetricOn (lpFiniteModes Vel) (velCore A c) := by
    intro x y
    exact BookProof.NavierStokesFlow.SignedShift.sirkNS_listH_symmetricOn (hopList A c)
      (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) x)
      (Submodule.inclusion (finiteModes_le_maxDom (velSym (velMu A c))) y)
  have hesa : EssentiallySelfAdjointOn (lpFiniteModes Vel) (velCore A c) :=
    BookProof.NavierStokesFlow.SignedShift.sirkNS_listH_essentiallySelfAdjointOn_core
      (hopList A c) (velSym_ge_one (velMu_nonneg A c))
  obtain ⟨Dom, G, hG⟩ := exists_isSelfAdjointExtension_of_esa (velCore A c)
    lpFiniteModes_dense hsym hesa
  choose X hX using fun j => exists_isShiftInvertC hG.2.1 (hγ j)
    (cshiftMap_surjective hG.2.1 hG.2.2 (hγ j))
  exact ⟨Dom, G, X, hG, hX,
    fun j => SirkComplexGeometryAux.numRange_subset_closedBall_of_shiftInvertC (hX j) hG.2.1 (hγ j),
    fun j _ V hViso => SirkComplexGeometryAux.crouzeix_domain_shiftInvertC (hX j) hG.2.1 (hγ j) V hViso⟩
#print axioms solution
