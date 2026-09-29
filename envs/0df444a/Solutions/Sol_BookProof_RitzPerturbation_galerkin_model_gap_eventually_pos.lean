-- Prove2me | solution 1 for BookProof.RitzPerturbation.galerkin_model_gap_eventually_pos
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:58:41.076753+00:00
-- url     : https://prove2.me/submissions/d5d27f2e-b862-4063-9072-ed970c7c7e35

import Definitions.Def_ChapterSirkRitzPerturbation
-- Adapted prerequisite proofs: Copyright 2026 Leonardo Pedro, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/tree/61595bc/BookProof
noncomputable section
open BookProof.RitzMinMax BookProof.RitzPerturbation BookProof.ChapterSirkRitzSpectrum BookProof.HermiteGalerkin
open Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
set_option autoImplicit false
set_option linter.unusedSectionVars false
private theorem ritzR_abs (T : F →L[ℂ] F) (x : F) :
    |rayleighVal T x| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc
    |rayleighVal T x| ≤ ‖x‖ * ‖T x‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm x (T x))
    _ ≤ ‖x‖ * (‖T‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg x)
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

private theorem ritzR_unit (T : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    |rayleighVal T x| ≤ ‖T‖ := by
  simpa only [hx, one_pow, mul_one] using ritzR_abs T x

private theorem ritzR_bddAbove (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    BddAbove (rayleighSetOn T S) := by
  refine ⟨‖T‖, ?_⟩
  rintro r ⟨x, hxS, hx, rfl⟩
  exact (abs_le.mp (ritzR_unit T hx)).2

private theorem ritzR_sup_le (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    rayleighSup T S ≤ ‖T‖ := by
  by_cases hne : (rayleighSetOn T S).Nonempty
  · apply csSup_le hne
    rintro r ⟨x, hxS, hx, rfl⟩
    exact (abs_le.mp (ritzR_unit T hx)).2
  · have he := Set.not_nonempty_iff_eq_empty.mp hne
    simpa only [rayleighSup, he, Real.sSup_empty] using norm_nonneg T

private theorem ritzR_le_sup (T : F →L[ℂ] F) (S : Submodule ℂ F) :
    -‖T‖ ≤ rayleighSup T S := by
  by_cases hne : (rayleighSetOn T S).Nonempty
  · obtain ⟨r, hr⟩ := hne
    obtain ⟨x, hxS, hx, rfl⟩ := hr
    exact (abs_le.mp (ritzR_unit T hx)).1.trans
      (le_csSup (ritzR_bddAbove T S) ⟨x, hxS, hx, rfl⟩)
  · have he := Set.not_nonempty_iff_eq_empty.mp hne
    simpa only [rayleighSup, he, Real.sSup_empty] using neg_nonpos.mpr (norm_nonneg T)

private theorem ritzR_bddBelow (T : F →L[ℂ] F) (k : ℕ) :
    BddBelow (minmaxSet T k) := by
  refine ⟨-‖T‖, ?_⟩
  rintro r ⟨S, hd, rfl⟩
  exact ritzR_le_sup T S

private theorem ritzP_ne (T : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : (rayleighSetOn T S).Nonempty := by
  letI : Nontrivial S := Module.nontrivial_of_finrank_pos hS
  obtain ⟨x, hx⟩ := exists_norm_eq (E := S) (show (0 : ℝ) ≤ 1 by norm_num)
  exact ⟨rayleighVal T (x : F), (x : F), x.property, hx, rfl⟩

private theorem ritzP_ne_congr (T T' : F →L[ℂ] F) {k : ℕ}
    (h : (minmaxSet T k).Nonempty) : (minmaxSet T' k).Nonempty := by
  obtain ⟨r, S, hd, hr⟩ := h
  exact ⟨rayleighSup T' S, S, hd, rfl⟩

private theorem ritzP_neIn_congr (T T' : F →L[ℂ] F) {W : Submodule ℂ F} {k : ℕ}
    (h : (minmaxSetIn T W k).Nonempty) : (minmaxSetIn T' W k).Nonempty := by
  obtain ⟨r, S, hSW, hd, hr⟩ := h
  exact ⟨rayleighSup T' S, S, hSW, hd, rfl⟩

private theorem ritzP_val (T T' : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    |rayleighVal T x - rayleighVal T' x| ≤ ‖T - T'‖ := by
  simpa only [rayleighVal, ContinuousLinearMap.sub_apply, inner_sub_right, Complex.sub_re]
    using ritzR_unit (T - T') hx

private theorem ritzP_sup (T T' : F →L[ℂ] F) {S : Submodule ℂ F}
    (hS : 0 < Module.finrank ℂ S) : rayleighSup T S ≤ rayleighSup T' S + ‖T - T'‖ := by
  apply csSup_le (ritzP_ne T hS)
  rintro r ⟨x, hxS, hx, rfl⟩
  have hm : rayleighVal T' x ≤ rayleighSup T' S :=
    le_csSup (ritzR_bddAbove T' S) ⟨x, hxS, hx, rfl⟩
  have hb := (abs_le.mp (ritzP_val T T' hx)).2
  linarith

private theorem ritzP_bddIn (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ) :
    BddBelow (minmaxSetIn T W k) := by
  refine ⟨-‖T‖, ?_⟩
  rintro r ⟨S, hSW, hd, rfl⟩
  exact ritzR_le_sup T S

private theorem ritzP_level (T T' : F →L[ℂ] F) (k : ℕ)
    (hne : (minmaxSet T' k).Nonempty) :
    minmaxLevel T k ≤ minmaxLevel T' k + ‖T - T'‖ := by
  have hh : minmaxLevel T k - ‖T - T'‖ ≤ minmaxLevel T' k := by
    apply le_csInf hne
    rintro r ⟨S, hd, rfl⟩
    have ha : minmaxLevel T k ≤ rayleighSup T S :=
      csInf_le (ritzR_bddBelow T k) ⟨S, hd, rfl⟩
    have hb := ritzP_sup T T' (show 0 < Module.finrank ℂ S by omega)
    linarith
  linarith

private theorem ritzP_levelIn (T T' : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (minmaxSetIn T' W k).Nonempty) :
    minmaxLevelIn T W k ≤ minmaxLevelIn T' W k + ‖T - T'‖ := by
  have hh : minmaxLevelIn T W k - ‖T - T'‖ ≤ minmaxLevelIn T' W k := by
    apply le_csInf hne
    rintro r ⟨S, hSW, hd, rfl⟩
    have ha : minmaxLevelIn T W k ≤ rayleighSup T S :=
      csInf_le (ritzP_bddIn T W k) ⟨S, hSW, hd, rfl⟩
    have hb := ritzP_sup T T' (show 0 < Module.finrank ℂ S by omega)
    linarith
  linarith

private theorem ritzP_absLevel (T T' : F →L[ℂ] F) (k : ℕ)
    (hne : (minmaxSet T k).Nonempty) :
    |minmaxLevel T k - minmaxLevel T' k| ≤ ‖T - T'‖ := by
  have ha := ritzP_level T T' k (ritzP_ne_congr T T' hne)
  have hb := ritzP_level T' T k hne
  rw [norm_sub_rev] at hb
  apply abs_le.mpr
  constructor <;> linarith

private theorem ritzP_absGap (T T' : F →L[ℂ] F)
    (hne0 : (minmaxSet T 0).Nonempty) (hne1 : (minmaxSet T 1).Nonempty) :
    |minmaxGap T - minmaxGap T'| ≤ 2 * ‖T - T'‖ := by
  obtain ⟨ha0, hb0⟩ := abs_le.mp (ritzP_absLevel T T' 0 hne0)
  obtain ⟨ha1, hb1⟩ := abs_le.mp (ritzP_absLevel T T' 1 hne1)
  unfold minmaxGap
  apply abs_le.mpr
  constructor <;> linarith

private theorem ritzG_smul (T : F →L[ℂ] F) (c : ℂ) (x : F) :
    rayleighVal T (c • x) = ‖c‖ ^ 2 * rayleighVal T x := by
  simp [rayleighVal, inner_smul_left, inner_smul_right, Complex.mul_re,
    Complex.mul_im, Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem ritzG_singleSet (T : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    rayleighSetOn T (Submodule.span ℂ {x}) = {rayleighVal T x} := by
  ext r
  constructor
  · rintro ⟨y, hy, hy1, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hc : ‖c‖ = 1 := by simpa [norm_smul, hx] using hy1
    simp [ritzG_smul, hc]
  · rintro rfl
    exact ⟨x, Submodule.mem_span_singleton_self x, hx, rfl⟩

private theorem ritzG_singleSup (T : F →L[ℂ] F) {x : F} (hx : ‖x‖ = 1) :
    rayleighSup T (Submodule.span ℂ {x}) = rayleighVal T x := by
  simp [rayleighSup, ritzG_singleSet T hx]

private theorem ritzG_zeroSet (T : F →L[ℂ] F) : minmaxSet T 0 = rayleighSet T := by
  ext r
  constructor
  · rintro ⟨S, hd, rfl⟩
    obtain ⟨_, x, hxS, hx, _⟩ := ritzP_ne T (show 0 < Module.finrank ℂ S by omega)
    have hx0 : x ≠ 0 := by intro he; simp [he] at hx
    have hs : S = Submodule.span ℂ {x} :=
      eq_span_singleton_of_mem_of_finrank_eq_one (by simpa using hd) hxS hx0
    exact ⟨x, hx, by rw [hs, ritzG_singleSup T hx]; rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hx0 : x ≠ 0 := by intro he; simp [he] at hx
    exact ⟨Submodule.span ℂ {x}, by simpa using finrank_span_singleton hx0,
      (ritzG_singleSup T hx).symm⟩

private theorem ritzG_mono (T : F →L[ℂ] F) {k l : ℕ} (hkl : k ≤ l)
    (hne : (minmaxSet T l).Nonempty) : minmaxLevel T k ≤ minmaxLevel T l := by
  apply le_csInf hne
  rintro r ⟨S, hd, rfl⟩
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := ℂ) (M := S)
    (n := k + 1) (by omega)
  let S' : Submodule ℂ F := Submodule.span ℂ (Set.range fun i => (f i : F))
  have hd' : Module.finrank ℂ S' = k + 1 := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range (S.subtype ∘ f))) = k + 1
    rw [finrank_span_eq_card (hf.map' S.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective))]
    exact Fintype.card_fin (k + 1)
  have hsub : S' ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (f i).property
  have hsup : rayleighSup T S' ≤ rayleighSup T S := by
    apply csSup_le (ritzP_ne T (show 0 < Module.finrank ℂ S' by omega))
    rintro r ⟨x, hxS, hx, rfl⟩
    exact le_csSup (ritzR_bddAbove T S) ⟨x, hsub hxS, hx, rfl⟩
  exact (csInf_le (ritzR_bddBelow T k) ⟨S', hd', rfl⟩).trans hsup

private theorem ritzG_dim (b : HilbertBasis ℕ ℂ F) (m : ℕ) :
    Module.finrank ℂ (galerkinSpan b m) = m := by
  have he : b '' {i | i < m} = Set.range (fun i : Fin m => b i) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.isLt, rfl⟩
  have hi := b.orthonormal.linearIndependent.comp (fun i : Fin m => (i : ℕ)) Fin.val_injective
  unfold galerkinSpan
  rw [he]
  simpa only [Function.comp_def, Fintype.card_fin] using finrank_span_eq_card hi

private theorem ritzG_neIn (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) {k m : ℕ}
    (hm : k + 1 ≤ m) : (minmaxSetIn T (galerkinSpan b m) k).Nonempty := by
  refine ⟨rayleighSup T (galerkinSpan b (k + 1)), galerkinSpan b (k + 1), ?_,
    ritzG_dim b (k + 1), rfl⟩
  apply Submodule.span_mono
  apply Set.image_mono
  intro i hi
  exact Nat.lt_of_lt_of_le hi hm

-- Adapted from leonardopedro/timepiece at commit 61595bc, ChapterSirkRitzMinMax.lean.
private theorem ritzG_valSub (T : F →L[ℂ] F) (y u : F) :
    rayleighVal T y - rayleighVal T u ≤ ‖T‖ * (‖y‖ + ‖u‖) * ‖y - u‖ := by
  have hsplit : (inner ℂ y (T y) : ℂ) - inner ℂ u (T u)
      = inner ℂ (y - u) (T y) + inner ℂ u (T (y - u)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  have h1 : rayleighVal T y - rayleighVal T u
      = (inner ℂ (y - u) (T y) : ℂ).re + (inner ℂ u (T (y - u)) : ℂ).re := by
    rw [rayleighVal, rayleighVal, ← Complex.sub_re, hsplit, Complex.add_re]
  have hb1 : (inner ℂ (y - u) (T y) : ℂ).re ≤ ‖y - u‖ * (‖T‖ * ‖y‖) := by
    calc (inner ℂ (y - u) (T y) : ℂ).re ≤ ‖(inner ℂ (y - u) (T y) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖y - u‖ * ‖T y‖ := norm_inner_le_norm _ _
      _ ≤ ‖y - u‖ * (‖T‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg _)
  have hb2 : (inner ℂ u (T (y - u)) : ℂ).re ≤ ‖u‖ * (‖T‖ * ‖y - u‖) := by
    calc (inner ℂ u (T (y - u)) : ℂ).re ≤ ‖(inner ℂ u (T (y - u)) : ℂ)‖ := Complex.re_le_norm _
      _ ≤ ‖u‖ * ‖T (y - u)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u‖ * (‖T‖ * ‖y - u‖) :=
          mul_le_mul_of_nonneg_left (T.le_opNorm _) (norm_nonneg _)
  rw [h1]
  nlinarith [hb1, hb2]


-- Adapted from leonardopedro/timepiece at commit 61595bc, Chapters SirkRitzMinMax, HermiteGalerkinFriedrichs, and H9.
private theorem ritzL_projMin (K : Submodule ℂ F) [K.HasOrthogonalProjection]
    (u w : F) (hw : w ∈ K) : ‖u - K.starProjection u‖ ≤ ‖u - w‖ := by
  rw [Submodule.starProjection_minimal]
  refine ciInf_le_of_le ⟨0, ?_⟩ (⟨w, hw⟩ : K) le_rfl
  rintro r ⟨x, rfl⟩
  positivity

private theorem ritzL_proj (b : HilbertBasis ℕ ℂ F) (u : F) :
    Tendsto (fun m : ℕ => (galerkinSpan b m).starProjection u) atTop (nhds u) := by
  have hm : Monotone (galerkinSpan b) := fun _ _ h =>
    Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)
  have hsub : Submodule.span ℂ (Set.range b) ≤ ⨆ m : ℕ, galerkinSpan b m := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem (i + 1) (Submodule.subset_span ⟨i, Nat.lt_succ_self i, rfl⟩)
  have hspan : Dense ((Submodule.span ℂ (Set.range b) : Submodule ℂ F) : Set F) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span
  have hdense : Dense ((⨆ m : ℕ, galerkinSpan b m : Submodule ℂ F) : Set F) := hspan.mono hsub
  rw [tendsto_iff_norm_sub_tendsto_zero, Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨w, hw, hwd⟩ := hdense.exists_dist_lt u heps
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _ hm.directed_le).mp hw
  refine ⟨N, fun n hn => ?_⟩
  have h1 := ritzL_projMin (galerkinSpan b n) u w (hm hn hN)
  have h2 : ‖u - w‖ < eps := by simpa [dist_eq_norm] using hwd
  have h3 : ‖(galerkinSpan b n).starProjection u - u‖ = ‖u - (galerkinSpan b n).starProjection u‖ := norm_sub_rev _ _
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _), h3]
  exact lt_of_le_of_lt h1 h2

private theorem ritzL_valSup (T : F →L[ℂ] F) {S : Submodule ℂ F} {x : F}
    (hx : x ∈ S) (hx1 : ‖x‖ = 1) : rayleighVal T x ≤ rayleighSup T S :=
  le_csSup (ritzR_bddAbove T S) ⟨x, hx, hx1, rfl⟩

private theorem ritzL_ne (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) :
    (minmaxSet T k).Nonempty :=
  ⟨rayleighSup T (galerkinSpan b (k + 1)), galerkinSpan b (k + 1), ritzG_dim b (k + 1), rfl⟩

private theorem ritzL_variational (T : F →L[ℂ] F) (W : Submodule ℂ F) (k : ℕ)
    (hne : (minmaxSetIn T W k).Nonempty) : minmaxLevel T k ≤ minmaxLevelIn T W k := by
  apply le_csInf hne
  rintro r ⟨S, hSW, hd, rfl⟩
  exact csInf_le (ritzR_bddBelow T k) ⟨S, hd, rfl⟩

private theorem ritzL_uniform (b : HilbertBasis ℕ ℂ F) (S : Submodule ℂ F)
    [FiniteDimensional ℂ S] {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ x ∈ S,
      ‖(galerkinSpan b m).starProjection x - x‖ ≤ ε * ‖x‖ := by
  classical
  set d := Module.finrank ℂ S with hd
  set e := stdOrthonormalBasis ℂ S with he
  set g : ℕ → (F →L[ℂ] F) :=
    fun m => (galerkinSpan b m).starProjection - ContinuousLinearMap.id ℂ F with hg
  have hgapp : ∀ (m : ℕ) (x : F), g m x = (galerkinSpan b m).starProjection x - x := by
    intro m x
    simp [hg]
  have htend : ∀ i : Fin d, ∀ᶠ m : ℕ in atTop, ‖g m ((e i : S) : F)‖ ≤ ε / (d + 1) := by
    intro i
    have h := ritzL_proj b ((e i : S) : F)
    rw [tendsto_iff_norm_sub_tendsto_zero] at h
    have hpos : 0 < ε / (d + 1) := by positivity
    have h2 := h.eventually (eventually_le_nhds hpos)
    filter_upwards [h2] with m hm
    rw [hgapp]
    exact hm
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i : Fin d, ‖g m ((e i : S) : F)‖ ≤ ε / (d + 1) :=
    eventually_all.2 htend
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp hall
  refine ⟨m₀, fun m hm x hx => ?_⟩
  have hbound := hm₀ m hm
  set y : S := ⟨x, hx⟩ with hy
  have hxsum : x = ∑ i : Fin d, (e.repr y i) • ((e i : S) : F) := by
    have h1 := e.sum_repr y
    have h2 := congrArg (fun z : S => (z : F)) h1
    simpa using h2.symm
  have hgx : g m x = ∑ i : Fin d, (e.repr y i) • (g m ((e i : S) : F)) := by
    rw [hxsum]
    simp [map_sum]
  have hcoef : ∀ i : Fin d, ‖e.repr y i‖ ≤ ‖x‖ := by
    intro i
    rw [e.repr_apply_apply]
    calc ‖(inner ℂ (e i) y : ℂ)‖ ≤ ‖(e i : S)‖ * ‖y‖ := norm_inner_le_norm _ _
      _ = ‖x‖ := by rw [e.orthonormal.1 i]; simp [hy]
  have hdd : (d : ℝ) / (d + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  calc ‖(galerkinSpan b m).starProjection x - x‖ = ‖g m x‖ := by rw [hgapp]
    _ = ‖∑ i : Fin d, (e.repr y i) • (g m ((e i : S) : F))‖ := by rw [hgx]
    _ ≤ ∑ i : Fin d, ‖(e.repr y i) • (g m ((e i : S) : F))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, ‖x‖ * (ε / (d + 1)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul]
        exact mul_le_mul (hcoef i) (hbound i) (norm_nonneg _) (norm_nonneg _)
    _ = (d : ℝ) * (‖x‖ * (ε / (d + 1))) := by simp [Finset.sum_const]
    _ = ((d : ℝ) / (d + 1)) * (ε * ‖x‖) := by field_simp
    _ ≤ 1 * (ε * ‖x‖) := mul_le_mul_of_nonneg_right hdd (by positivity)
    _ = ε * ‖x‖ := one_mul _

private theorem ritzL_approx (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    {S : Submodule ℂ F} {k : ℕ} (hrank : Module.finrank ℂ S = k + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∃ S' : Submodule ℂ F, S' ≤ galerkinSpan b m ∧
      Module.finrank ℂ S' = k + 1 ∧ rayleighSup T S' ≤ rayleighSup T S + ε := by
  classical
  have hfd : FiniteDimensional ℂ S := .of_finrank_pos (by rw [hrank]; omega)
  set c : ℝ := ‖T‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  set δ : ℝ := min (1 / 2) (ε / (8 * c + 8)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδeps : 8 * c * δ ≤ ε := by
    have h1 : δ ≤ ε / (8 * c + 8) := min_le_right _ _
    have h2 : (0 : ℝ) < 8 * c + 8 := by linarith
    calc 8 * c * δ ≤ 8 * c * (ε / (8 * c + 8)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ ε := by
          rw [mul_div_assoc', div_le_iff₀ h2]
          nlinarith [hε.le]
  obtain ⟨m₀, hm₀⟩ := ritzL_uniform b S hδpos
  refine ⟨m₀, fun m hm => ?_⟩
  set P := (galerkinSpan b m).starProjection with hP
  have hbnd : ∀ x ∈ S, ‖P x - x‖ ≤ δ * ‖x‖ := hm₀ m hm
  have hinj : Function.Injective ((P : F →ₗ[ℂ] F) ∘ₗ S.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hx⟩ hzero
    have h0 : P x = 0 := by simpa using hzero
    have h2 := hbnd x hx
    rw [h0, zero_sub, norm_neg] at h2
    have hx0 : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    ext
    simpa using hx0
  have hrk : Module.finrank ℂ (S.map (P : F →ₗ[ℂ] F)) = k + 1 := by
    have hr : LinearMap.range ((P : F →ₗ[ℂ] F) ∘ₗ S.subtype) = S.map (P : F →ₗ[ℂ] F) := by
      rw [LinearMap.range_comp]
      simp
    rw [← hr, LinearMap.finrank_range_of_inj hinj, hrank]
  refine ⟨S.map (P : F →ₗ[ℂ] F), ?_, hrk, ?_⟩
  · rintro y ⟨x, -, rfl⟩
    exact (galerkinSpan b m).starProjection_apply_mem x
  · refine csSup_le
      (ritzP_ne T (S := S.map (P : F →ₗ[ℂ] F)) (by rw [hrk]; omega)) ?_
    rintro t ⟨y, hy, hy1, rfl⟩
    obtain ⟨x, hxS, rfl⟩ := hy
    simp only [ContinuousLinearMap.coe_coe] at hy1 ⊢
    have hxnorm : ‖P x - x‖ ≤ δ * ‖x‖ := hbnd x hxS
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hy1
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have habs : |‖x‖ - 1| ≤ δ * ‖x‖ := by
      have h1 := abs_norm_sub_norm_le x (P x)
      rw [hy1, norm_sub_rev] at h1
      exact h1.trans hxnorm
    have hxle : ‖x‖ ≤ 2 := by
      have h2 := abs_le.mp habs
      nlinarith [h2.2]
    set u : F := (‖x‖⁻¹ : ℂ) • x with hu
    have hunorm : ‖u‖ = 1 := by
      rw [hu, norm_smul]
      simp [hxpos.ne']
    have huS : u ∈ S := S.smul_mem _ hxS
    have hxu : ‖x - u‖ = |‖x‖ - 1| := by
      have hxe : x - u = ((1 - ‖x‖⁻¹ : ℝ) : ℂ) • x := by
        rw [hu]
        push_cast
        module
      have key : (1 - ‖x‖⁻¹) * ‖x‖ = ‖x‖ - 1 := by field_simp
      rw [hxe, norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      calc |1 - ‖x‖⁻¹| * ‖x‖ = |1 - ‖x‖⁻¹| * |‖x‖| := by rw [abs_of_pos hxpos]
        _ = |(1 - ‖x‖⁻¹) * ‖x‖| := (abs_mul _ _).symm
        _ = |‖x‖ - 1| := by rw [key]
    have hyu : ‖P x - u‖ ≤ 2 * (δ * ‖x‖) := by
      calc ‖P x - u‖ ≤ ‖P x - x‖ + ‖x - u‖ := by
            simpa using norm_sub_le_norm_sub_add_norm_sub (P x) x u
        _ ≤ δ * ‖x‖ + δ * ‖x‖ := by rw [hxu]; linarith [habs]
        _ = 2 * (δ * ‖x‖) := by ring
    have hdiff := ritzG_valSub T (P x) u
    rw [hy1, hunorm] at hdiff
    have hbound2 : rayleighVal T (P x) - rayleighVal T u ≤ ε := by
      have h4 : ‖P x - u‖ ≤ 4 * δ := by nlinarith [hyu, hxle, hδpos.le]
      calc rayleighVal T (P x) - rayleighVal T u ≤ c * (1 + 1) * ‖P x - u‖ := hdiff
        _ ≤ c * (1 + 1) * (4 * δ) := mul_le_mul_of_nonneg_left h4 (by linarith)
        _ = 8 * c * δ := by ring
        _ ≤ ε := hδeps
    have hle := ritzL_valSup T huS hunorm
    linarith

private theorem ritzL_converge (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) (k : ℕ) :
    Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) k) atTop
      (nhds (minmaxLevel T k)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt (ritzL_ne T b k)
    (show minmaxLevel T k < minmaxLevel T k + ε / 2 by linarith)
  obtain ⟨S, hrank, rfl⟩ := ht
  obtain ⟨m₀, hm₀⟩ := ritzL_approx T b hrank (half_pos hε)
  refine ⟨max m₀ (k + 1), fun m hm => ?_⟩
  have hlow : minmaxLevel T k ≤ minmaxLevelIn T (galerkinSpan b m) k :=
    ritzL_variational T _ k (ritzG_neIn T b (le_of_max_le_right hm))
  obtain ⟨S', hS'le, hS'rank, hS'sup⟩ := hm₀ m (le_of_max_le_left hm)
  have hup : minmaxLevelIn T (galerkinSpan b m) k ≤ rayleighSup T S' :=
    csInf_le (ritzP_bddIn T _ k) ⟨S', hS'le, hS'rank, rfl⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

private theorem ritzL_gap (T : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F) :
    Tendsto (fun m : ℕ => minmaxLevelIn T (galerkinSpan b m) 1
        - minmaxLevelIn T (galerkinSpan b m) 0) atTop
      (nhds (minmaxLevel T 1 - minmaxLevel T 0)) :=
  ((ritzL_converge T b 1).sub (ritzL_converge T b 0))

theorem solution (T T' : F →L[ℂ] F) (b : HilbertBasis ℕ ℂ F)
    {eps : ℝ} (hd : ‖T - T'‖ ≤ eps) (hgap : 2 * eps < minmaxGap T) :
    ∀ᶠ m : ℕ in atTop, 0 < minmaxLevelIn T' (galerkinSpan b m) 1
      - minmaxLevelIn T' (galerkinSpan b m) 0 := by
  have hb := (abs_le.mp (ritzP_absGap T' T (ritzL_ne T' b 0) (ritzL_ne T' b 1))).1
  rw [norm_sub_rev] at hb
  have hp : 0 < minmaxGap T' := by linarith
  exact (ritzL_gap T' b).eventually_const_lt hp

#print axioms solution
