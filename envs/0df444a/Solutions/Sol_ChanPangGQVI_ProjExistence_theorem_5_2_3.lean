-- Prove2me | solution 3 for ChanPangGQVI.ProjExistence.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T06:57:26.981966+00:00
-- url     : https://prove2.me/submissions/bb134eca-773a-4eb0-bcc3-3b2d1cf96547

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_GQVI
import Theorems.Thm_Brouwer_exists_fixedPoint_euclideanSpace

-- carved verbatim out of submission 08ed2756-557a-470f-8493-8c93e6b779c8, lines 936-949

section
open Metric Set MeasureTheory
open ChanPangGQVI

theorem brouwer_core {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  classical
  let φ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hconv' : Convex ℝ (φ '' K) :=
    hKconv.linear_image (φ : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  have hcont : ContinuousOn (φ ∘ f ∘ φ.symm) (φ '' K) := by
    refine φ.continuous.comp_continuousOn (hf.comp φ.symm.continuous.continuousOn ?_)
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  have hmaps : MapsTo (φ ∘ f ∘ φ.symm) (φ '' K) (φ '' K) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨f y, hfK hy, by simp⟩
  obtain ⟨x, ⟨y, hyK, rfl⟩, hx⟩ :=
    Brouwer.exists_fixedPoint_euclideanSpace hconv' (hKcpt.image φ.continuous) (hKne.image φ) _ hcont hmaps
  refine ⟨y, hyK, ?_⟩
  apply φ.injective
  simpa using hx

end

section
open Metric Set MeasureTheory
open ChanPangGQVI
open Filter Topology
open scoped RealInnerProductSpace

def IsVProj {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) (z p : EuclideanSpace ℝ (Fin n)) :
    Prop :=
  p ∈ S ∧ ∀ w ∈ S, ⟪z - p, w - p⟫ ≤ 0

theorem exists_vproj {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))} (hne : S.Nonempty)
    (hcl : IsClosed S) (hcv : Convex ℝ S) (z : EuclideanSpace ℝ (Fin n)) :
    ∃ p, IsVProj S z p := by
  obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hcv z
  exact ⟨v, hv, (norm_eq_iInf_iff_real_inner_le_zero hcv hv).1 hmin⟩

theorem vproj_unique {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {z p q : EuclideanSpace ℝ (Fin n)} (hp : IsVProj S z p) (hq : IsVProj S z q) : p = q := by
  have h1 := hp.2 q hq.1
  have h2 := hq.2 p hp.1
  have e1 : ⟪z - q, p - q⟫ = -⟪z - q, q - p⟫ := by
    rw [← inner_neg_right, neg_sub]
  have e2 : ⟪z - p, q - p⟫ - ⟪z - q, q - p⟫ = ⟪q - p, q - p⟫ := by
    rw [← inner_sub_left]
    congr 1
    abel
  have h3 : ⟪q - p, q - p⟫ ≤ 0 := by linarith
  have h4 : q - p = 0 := real_inner_self_nonpos.1 h3
  exact (sub_eq_zero.1 h4).symm

theorem vproj_le_infDist {n : ℕ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {z p : EuclideanSpace ℝ (Fin n)} (hp : IsVProj S z p) (w : EuclideanSpace ℝ (Fin n)) :
    ⟪z - p, w - p⟫ ≤ ‖z - p‖ * infDist w S := by
  have hne : S.Nonempty := ⟨p, hp.1⟩
  by_cases h0 : ‖z - p‖ = 0
  · have hz : z - p = 0 := norm_eq_zero.1 h0
    simp [hz]
  have hpos : 0 < ‖z - p‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
  have key : ⟪z - p, w - p⟫ / ‖z - p‖ ≤ infDist w S := by
    rw [le_infDist hne]
    intro w' hw'
    rw [div_le_iff₀' hpos]
    have h1 := hp.2 w' hw'
    have e : ⟪z - p, w - p⟫ = ⟪z - p, w' - p⟫ + ⟪z - p, w - w'⟫ := by
      rw [← inner_add_right]
      congr 1
      abel
    have h2 : ⟪z - p, w - w'⟫ ≤ ‖z - p‖ * ‖w - w'‖ := real_inner_le_norm _ _
    rw [dist_eq_norm]
    linarith
  rwa [div_le_iff₀' hpos] at key

theorem thm52_core {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C) (hC_convex : Convex ℝ C)
    (h_i : ∀ x ∈ C, K x ⊆ C)
    (h_ii : ContinuousOn f C)
    (h_iii_nonempty : ∀ x ∈ C, (K x).Nonempty)
    (h_iii_upper : UpperHemicontinuousOn K C) (h_iii_lower : LowerHemicontinuousOn K C)
    (h_iii_convex : ∀ x ∈ C, Convex ℝ (K x))
    (hK_closed : ∀ x ∈ C, IsClosed (K x)) :
    ∃ x y, ChanPangGQVI.Shared.IsGQVISolution K (fun z => {f z}) x y := by
  classical
  have hex : ∀ x ∈ C, ∃ p, IsVProj (K x) (x - f x) p := fun x hx =>
    exists_vproj (h_iii_nonempty x hx) (hK_closed x hx) (h_iii_convex x hx) _
  let g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => if h : x ∈ C then (hex x h).choose else x
  have hg : ∀ x ∈ C, IsVProj (K x) (x - f x) (g x) := by
    intro x hx
    simp only [g, dif_pos hx]
    exact (hex x hx).choose_spec
  have hmaps : MapsTo g C C := fun x hx => h_i x hx (hg x hx).1
  have hcont : ContinuousOn g C := by
    intro x0 hx0
    apply hC_compact.tendsto_nhds_of_unique_mapClusterPt
      (eventually_nhdsWithin_of_forall hmaps)
    intro p _ hclp
    set l := 𝓝[C] x0 with hl
    set F := l ⊓ comap g (𝓝 p) with hF
    have : F.NeBot := by
      rw [inf_neBot_iff]
      intro a ha b hb
      obtain ⟨t, ht, htb⟩ := mem_comap.1 hb
      have hfr := (mapClusterPt_iff_frequently.1 hclp) t ht
      obtain ⟨x, hxt, hxa⟩ := (hfr.and_eventually ha).exists
      exact ⟨x, hxa, htb hxt⟩
    have hFl : F ≤ l := inf_le_left
    have hgF : Tendsto g F (𝓝 p) := tendsto_comap.mono_left inf_le_right
    have hxF : Tendsto (fun x => x) F (𝓝 x0) :=
      tendsto_id.mono_left (hFl.trans nhdsWithin_le_nhds)
    have hfF : Tendsto f F (𝓝 (f x0)) := (h_ii x0 hx0).tendsto.mono_left hFl
    have hzF : Tendsto (fun x => x - f x) F (𝓝 (x0 - f x0)) := hxF.sub hfF
    have hCF : ∀ᶠ x in F, x ∈ C := hFl self_mem_nhdsWithin
    have hne0 := h_iii_nonempty x0 hx0
    -- (a) the limit point lies in `K x0`
    have hpK : p ∈ K x0 := by
      by_contra hp
      have hpos : 0 < infDist p (K x0) := by
        rw [← infDist_pos_iff_notMem_closure hne0, (hK_closed x0 hx0).closure_eq]
        exact hp
      set r := infDist p (K x0) with hr
      have ht : thickening (r / 2) (K x0) ∈ 𝓝ˢ (K x0) :=
        isOpen_thickening.mem_nhdsSet.2 (self_subset_thickening (by linarith) _)
      have hev : ∀ᶠ x in l, thickening (r / 2) (K x0) ∈ 𝓝ˢ (K x) :=
        upperHemicontinuousWithinAt_iff.1 (upperHemicontinuousOn_iff.1 h_iii_upper x0 hx0) _ ht
      have hev2 : ∀ᶠ x in F, infDist (g x) (K x0) < r / 2 := by
        filter_upwards [hFl hev, hCF] with x hx hxC
        have hmem := subset_of_mem_nhdsSet hx (hg x hxC).1
        exact (mem_thickening_iff_infDist_lt hne0).1 hmem
      have hlim : Tendsto (fun x => infDist (g x) (K x0)) F (𝓝 r) :=
        ((continuous_infDist_pt (K x0)).tendsto p).comp hgF
      have : r ≤ r / 2 := le_of_tendsto hlim (hev2.mono fun x hx => hx.le)
      linarith
    -- (b) the variational inequality passes to the limit
    have hVI : ∀ w ∈ K x0, ⟪(x0 - f x0) - p, w - p⟫ ≤ 0 := by
      intro w hw
      have hd : Tendsto (fun x => infDist w (K x)) F (𝓝 0) := by
        rw [Metric.tendsto_nhds]
        intro ε hε
        have hev : ∀ᶠ x in l, (K x ∩ ball w ε).Nonempty :=
          lowerHemicontinuousWithinAt_iff.1 (lowerHemicontinuousOn_iff.1 h_iii_lower x0 hx0)
            _ isOpen_ball ⟨w, hw, mem_ball_self hε⟩
        filter_upwards [hFl hev] with x hx
        obtain ⟨y, hyK, hyb⟩ := hx
        have h0 : 0 ≤ infDist w (K x) := infDist_nonneg
        rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
        calc infDist w (K x) ≤ dist w y := infDist_le_dist_of_mem hyK
          _ < ε := by rw [dist_comm]; exact hyb
      have hineq : ∀ᶠ x in F,
          ⟪(x - f x) - g x, w - g x⟫ ≤ ‖(x - f x) - g x‖ * infDist w (K x) := by
        filter_upwards [hCF] with x hx
        exact vproj_le_infDist (hg x hx) w
      have hL1 : Tendsto (fun x => ⟪(x - f x) - g x, w - g x⟫) F
          (𝓝 ⟪(x0 - f x0) - p, w - p⟫) :=
        (hzF.sub hgF).inner (tendsto_const_nhds.sub hgF)
      have hR : Tendsto (fun x => ‖(x - f x) - g x‖ * infDist w (K x)) F
          (𝓝 (‖(x0 - f x0) - p‖ * 0)) :=
        (hzF.sub hgF).norm.mul hd
      rw [mul_zero] at hR
      exact le_of_tendsto_of_tendsto hL1 hR hineq
    exact vproj_unique ⟨hpK, hVI⟩ (hg x0 hx0)
  obtain ⟨x, hxC, hfx⟩ := brouwer_core hC_convex hC_compact hC_nonempty g hcont hmaps
  have hx := hg x hxC
  rw [hfx] at hx
  refine ⟨x, f x, hx.1, rfl, ?_⟩
  intro x' hx'
  have h1 := hx.2 x' hx'
  have e : (x - f x) - x = -(f x) := by abel
  rw [e, inner_neg_left, real_inner_comm] at h1
  linarith

end

section
open Metric Set MeasureTheory

theorem solution {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C) (hC_convex : Convex ℝ C)
    (h_i : ∀ x ∈ C, K x ⊆ C)
    (h_ii : ContinuousOn f C)
    (h_iii_nonempty : ∀ x ∈ C, (K x).Nonempty)
    (h_iii_upper : UpperHemicontinuousOn K C) (h_iii_lower : LowerHemicontinuousOn K C)
    (h_iii_convex : ∀ x ∈ C, Convex ℝ (K x))
    (hK_closed : ∀ x ∈ C, IsClosed (K x)) :
    ∃ x y, ChanPangGQVI.Shared.IsGQVISolution K (fun z => {f z}) x y := by
  exact thm52_core K f C hC_nonempty hC_compact hC_convex h_i h_ii h_iii_nonempty h_iii_upper h_iii_lower h_iii_convex hK_closed

end
