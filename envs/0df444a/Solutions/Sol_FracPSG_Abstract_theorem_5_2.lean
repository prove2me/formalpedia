-- Prove2me | solution 1 for FracPSG.Abstract.theorem_5_2
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T06:28:09.486131+00:00
-- url     : https://prove2.me/submissions/93ce49f1-6e62-4b46-b800-72ce1532bf82

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_StandingAssumptions
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_FracPSG_Abstract_Basic

open Filter Topology

section

open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

namespace FracPSG.Abstract.Fresh

end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
variable {h : K → EReal} {z : ℕ → K} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ}
variable {ilo ihi : ℤ} {lam : ℤ → ℝ}

theorem value_finite (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h2 : H2 h z β ε Δ ilo ihi lam) (n : ℕ) : h (z n) ≠ ⊤ ∧ h (z n) ≠ ⊥ := by
  obtain ⟨v, hv, _⟩ := h2 n
  exact ⟨hv.1, hs.proper.1 _⟩

theorem value_coe (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h2 : H2 h z β ε Δ ilo ihi lam) (n : ℕ) :
    ((h (z n)).toReal : EReal) = h (z n) :=
  EReal.coe_toReal (value_finite hs h2 n).1 (value_finite hs h2 n).2

theorem values_antitone (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) : Antitone (fun n => h (z n)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hp : (0 : EReal) ≤ ((α n * Δ n ^ 2 : ℝ) : EReal) := by
    exact_mod_cast mul_nonneg (hs.alpha_pos n).le (sq_nonneg _)
  exact (le_add_of_nonneg_right hp).trans (h1 n)

theorem value_decrease (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam) (n : ℕ) :
    (h (z (n+1))).toReal + α n * Δ n ^ 2 ≤ (h (z n)).toReal := by
  have hh := h1 n
  rw [← value_coe hs h2 (n+1), ← value_coe hs h2 n, ← EReal.coe_add] at hh
  exact_mod_cast hh

theorem real_values_antitone (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam) :
    Antitone (fun n => (h (z n)).toReal) := by
  intro i j hij
  have hh := values_antitone hs h1 hij
  change h (z j) ≤ h (z i) at hh
  rw [← value_coe hs h2 j, ← value_coe hs h2 i] at hh
  exact_mod_cast hh
end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
variable {h : K → EReal} {z : ℕ → K} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ}
variable {ilo ihi : ℤ} {lam : ℤ → ℝ}

theorem exists_attentive_value_limit (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam) (h3 : H3 h z) :
    ∃ zt ∈ clusterSet z, h zt ≠ ⊤ ∧ h zt ≠ ⊥ ∧
      Tendsto (fun n => (h (z n)).toReal) atTop (𝓝 (h zt).toReal) ∧
      Tendsto (fun n => h (z n)) atTop (𝓝 (h zt)) := by
  obtain ⟨k, hk, zt, hzk, hvk⟩ := h3
  have hle : h zt ≤ h (z 0) := le_of_tendsto hvk (Filter.Eventually.of_forall
    (fun n => values_antitone hs h1 (Nat.zero_le (k n))))
  have ht : h zt ≠ ⊤ := ne_top_of_le_ne_top (value_finite hs h2 0).1 hle
  have hb : h zt ≠ ⊥ := hs.proper.1 zt
  have hrk : Tendsto (fun n => (h (z (k n))).toReal) atTop (𝓝 (h zt).toReal) :=
    (EReal.tendsto_toReal ht hb).comp hvk
  have hr : Tendsto (fun n => (h (z n)).toReal) atTop (𝓝 (h zt).toReal) :=
    (tendsto_iff_tendsto_subseq_of_antitone (real_values_antitone hs h1 h2)
      hk.tendsto_atTop).2 hrk
  refine ⟨zt, ?_, ht, hb, hr, ?_⟩
  · exact hzk.mapClusterPt.of_comp hk.tendsto_atTop
  · have hh := EReal.tendsto_coe.mpr hr
    simpa only [value_coe hs h2, EReal.coe_toReal ht hb] using hh

end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
variable {h : K → EReal} {z : ℕ → K} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ}
variable {ilo ihi : ℤ} {lam : ℤ → ℝ}

theorem uniform_value_limit (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam) (h3 : H3 h z)
    (hc : ∀ x ∈ clusterSet z, ∀ y ∈ clusterSet z, h x = h y) :
    ∃ l : ℝ, Tendsto (fun n => (h (z n)).toReal) atTop (𝓝 l) ∧
      Tendsto (fun n => h (z n)) atTop (𝓝 (l : EReal)) ∧
      (∀ x ∈ clusterSet z, h x = (l : EReal)) ∧
      ∀ n, l ≤ (h (z n)).toReal := by
  obtain ⟨zt, hzt, ht, hb, hr, he⟩ := exists_attentive_value_limit hs h1 h2 h3
  refine ⟨(h zt).toReal, hr, ?_, ?_, ?_⟩
  · simpa only [EReal.coe_toReal ht hb] using he
  · intro x hx
    rw [hc x hx zt hzt, EReal.coe_toReal ht hb]
  · intro n
    exact le_of_tendsto hr (Filter.eventually_atTop.2 ⟨n, fun m hm =>
      real_values_antitone hs h1 h2 hm⟩)

theorem gap_decrease (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam) (l : ℝ) (n : ℕ) :
    α n * Δ n ^ 2 ≤ ((h (z n)).toReal-l) - ((h (z (n+1))).toReal-l) := by
  linarith [value_decrease hs h1 h2 n]
end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh

theorem desingularizer_mono {a b : ℝ} {φ : ℝ → ℝ}
    (h : IsDesingularizer b φ) (hab : a ≤ b) : IsDesingularizer a φ := by
  have hc : Set.Ico (0:ℝ) a ⊆ Set.Ico 0 b := fun _ hx => ⟨hx.1, hx.2.trans_le hab⟩
  have ho : Set.Ioo (0:ℝ) a ⊆ Set.Ioo 0 b := fun _ hx => ⟨hx.1, hx.2.trans_le hab⟩
  exact ⟨h.1.mono hc, h.2.1.subset hc (convex_Ico _ _),
    fun x hx => h.2.2.1 x (hc hx), h.2.2.2.1, h.2.2.2.2.1.mono ho,
    fun x hx => h.2.2.2.2.2 x (ho hx)⟩

theorem desingularizer_differentiable {a : ℝ} {φ : ℝ → ℝ}
    (h : IsDesingularizer a φ) {x : ℝ} (hx : x ∈ Set.Ioo 0 a) :
    DifferentiableAt ℝ φ x :=
  (h.2.2.2.2.1.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hx)

theorem concave_finset_sum {ι : Type*} (s : Finset ι) (φ : ι → ℝ → ℝ)
    {a : ℝ} (h : ∀ i ∈ s, ConcaveOn ℝ (Set.Ico 0 a) (φ i)) :
    ConcaveOn ℝ (Set.Ico 0 a) (fun x => ∑ i ∈ s, φ i x) := by
  refine ⟨convex_Ico _ _, ?_⟩
  intro x hx y hy u v hu hv huv
  simpa only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib] using
    Finset.sum_le_sum (fun i hi => (h i hi).2 hx hy hu hv huv)

theorem desingularizer_sum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (φ : ι → ℝ → ℝ) {a : ℝ} (h : ∀ i ∈ s, IsDesingularizer a (φ i)) :
    IsDesingularizer a (fun x => ∑ i ∈ s, φ i x) := by
  refine ⟨continuousOn_finsetSum _ (fun i hi => (h i hi).1),
    concave_finset_sum s φ (fun i hi => (h i hi).2.1),
    fun x hx => Finset.sum_nonneg (fun i hi => (h i hi).2.2.1 x hx), ?_,
    ContDiffOn.sum (fun i hi => (h i hi).2.2.2.2.1), ?_⟩
  · exact Finset.sum_eq_zero (fun i hi => (h i hi).2.2.2.1)
  · intro x hx
    rw [deriv_fun_sum (fun i hi => desingularizer_differentiable (h i hi) hx)]
    exact Finset.sum_pos (fun i hi => (h i hi).2.2.2.2.2 x hx) hs
end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh

theorem concave_drop {eta r s : ℝ} {φ : ℝ → ℝ}
    (hφ : IsDesingularizer eta φ) (hr : r ∈ Set.Ioo 0 eta)
    (hs : 0 ≤ s) (hsr : s ≤ r) :
    deriv φ r * (r-s) ≤ φ r - φ s := by
  rcases hsr.eq_or_lt with he | he
  · subst s; simp
  · have hh := hφ.2.1.deriv_le_slope ⟨hs, he.trans hr.2⟩ ⟨hr.1.le, hr.2⟩ he
      (desingularizer_differentiable hφ hr)
    rw [slope_def_field] at hh
    exact (le_div_iff₀ (sub_pos.mpr he)).mp hh

theorem kl_recurrence_scalar {a b g d v D F R S : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hg : 0 < g) (hD : 0 < D)
    (_hd : 0 ≤ d) (_hv : 0 ≤ v) (hS : 0 ≤ S)
    (hgab : g ≤ a*b) (hdec : a*d^2 ≤ R) (hconc : D*R ≤ F)
    (hkl : 1 ≤ D*v) (herr : b*v ≤ S) :
    2*d ≤ F/g+S := by
  have hbDS : b ≤ D*S := by nlinarith
  have hR : 0 ≤ R := (mul_nonneg ha.le (sq_nonneg d)).trans hdec
  have hF : 0 ≤ F := (mul_nonneg hD.le hR).trans hconc
  have hsq : g*d^2 ≤ F*S := calc
    g*d^2 ≤ a*b*d^2 := mul_le_mul_of_nonneg_right hgab (sq_nonneg _)
    _ ≤ a*(D*S)*d^2 := by nlinarith [mul_nonneg ha.le (sq_nonneg d)]
    _ = (D*(a*d^2))*S := by ring
    _ ≤ (D*R)*S := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdec hD.le) hS
    _ ≤ F*S := mul_le_mul_of_nonneg_right hconc hS
  have hp : 0 ≤ F/g := div_nonneg hF hg.le
  have hds : d^2 ≤ (F/g)*S := by
    have hh : d^2 ≤ (F*S)/g := (le_div_iff₀ hg).2 (by nlinarith [hsq])
    convert hh using 1
    ring
  nlinarith [sq_nonneg (F/g-S)]
end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
variable {h : K → EReal} {z : ℕ → K} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ}
variable {ilo ihi : ℤ} {lam : ℤ → ℝ}

theorem native_recurrence (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam)
    {l eta g : ℝ} {φ : ℝ → ℝ} (hg : 0 < g)
    (hl : ∀ n, l ≤ (h (z n)).toReal) (hφ : IsDesingularizer eta φ)
    (n : ℕ) (hsmall : (h (z n)).toReal-l < eta) (hgab : g ≤ α n*β n)
    (hkl : 0 < (h (z n)).toReal-l → ∀ v ∈ LimitingSubdiff h (z n),
      1 ≤ deriv φ ((h (z n)).toReal-l)*‖v‖) :
    2*Δ n ≤ (φ ((h (z n)).toReal-l)-φ ((h (z (n+1))).toReal-l))/g +
      (∑ i ∈ Finset.Icc ilo ihi, lam i*Δ ((n:ℤ)-i)) + ε n := by
  let r := (h (z n)).toReal-l
  let s := (h (z (n+1))).toReal-l
  have hr : 0 ≤ r := sub_nonneg.mpr (hl n)
  have hsn : 0 ≤ s := sub_nonneg.mpr (hl (n+1))
  have hsr : s ≤ r := sub_le_sub_right (real_values_antitone hs h1 h2 (Nat.le_succ n)) l
  have hdec : α n*Δ n^2 ≤ r-s := gap_decrease hs h1 h2 l n
  have hsum : 0 ≤ ∑ i ∈ Finset.Icc ilo ihi, lam i*Δ ((n:ℤ)-i) :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hs.lam_nonneg i hi) (hs.delta_nonneg _))
  by_cases hp : 0 < r
  · obtain ⟨v, hv, herr⟩ := h2 n
    have hh := kl_recurrence_scalar (hs.alpha_pos n) (hs.beta_pos n) hg
      (hφ.2.2.2.2.2 r ⟨hp,hsmall⟩) (hs.delta_nonneg n) (norm_nonneg v)
      (add_nonneg hsum (hs.eps_nonneg n)) hgab hdec
      (concave_drop hφ ⟨hp,hsmall⟩ hsn hsr) (hkl hp v hv) herr
    simpa only [add_assoc] using hh
  · have hz : r=0 := le_antisymm (le_of_not_gt hp) hr
    have hsz : s=0 := by linarith
    have hmul : α n * Δ n^2 = 0 := le_antisymm (by simpa [hz,hsz] using hdec)
      (mul_nonneg (hs.alpha_pos n).le (sq_nonneg _))
    have hd : Δ n=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hmul).resolve_left (ne_of_gt (hs.alpha_pos n)))
    change 2*Δ n ≤ (φ r-φ s)/g + _ + _
    rw [hz, hsz, hd]
    simp only [mul_zero, sub_self, zero_div, zero_add]
    exact add_nonneg hsum (hs.eps_nonneg n)
end FracPSG.Abstract.Fresh
end

section

open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

namespace FracPSG.Abstract.Fresh

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem finite_kl_cover {h : K → EReal} {Ω : Set K}
    (hc : IsCompact Ω) (hne : Ω.Nonempty)
    (hkl : ∀ x ∈ Ω, HasKLProperty h x) :
    ∃ (s : Finset Ω), s.Nonempty ∧ ∃ η : ℝ, 0 < η ∧
      ∃ (radius : Ω → ℝ) (V : Ω → Set K) (φ : Ω → ℝ → ℝ),
        (∀ i, 0 < radius i ∧ IsOpen (V i) ∧
          IsDesingularizer (radius i) (φ i) ∧ KLIneq h i (radius i) (V i) (φ i)) ∧
        (∀ i ∈ s, η ≤ radius i) ∧ Ω ⊆ ⋃ i ∈ s, V i := by
  classical
  choose radius hr W hW φ hφ hineq using fun i : Ω => hkl i i.2
  let V : Ω → Set K := fun i => interior (W i)
  have hopen : ∀ i, IsOpen (V i) := fun _ => isOpen_interior
  have hcover : Ω ⊆ ⋃ i : Ω, V i := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hW ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover V hopen hcover
  have hsne : s.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact ⟨i, hi⟩
  refine ⟨s, hsne, s.inf' hsne radius, ?_, radius, V, φ, ?_, ?_, hs⟩
  · exact (Finset.lt_inf'_iff hsne).mpr fun i _ => hr i
  · intro i
    refine ⟨hr i, hopen i, hφ i, ?_⟩
    intro x hx hlow hhigh v hv
    exact hineq i x (interior_subset hx) hlow hhigh v hv
  · intro i hi
    exact Finset.inf'_le radius hi

end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem uniform_kl {h : K → EReal} {Ω : Set K} {l : ℝ}
    (hc : IsCompact Ω) (hne : Ω.Nonempty) (hl : ∀ x ∈ Ω, h x = (l : EReal))
    (hkl : ∀ x ∈ Ω, HasKLProperty h x) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ U : Set K, IsOpen U ∧ Ω ⊆ U ∧
      ∃ φ : ℝ → ℝ, IsDesingularizer eta φ ∧
      ∀ x ∈ U, ∀ r : ℝ, h x = ((l+r : ℝ) : EReal) → 0 < r → r < eta →
        ∀ v ∈ LimitingSubdiff h x, 1 ≤ deriv φ r * ‖v‖ := by
  classical
  obtain ⟨s, hs, eta, heta, radius, V, phi, hh, he, hcover⟩ := finite_kl_cover hc hne hkl
  have hphi : ∀ i ∈ s, IsDesingularizer eta (phi i) :=
    fun i hi => desingularizer_mono (hh i).2.2.1 (he i hi)
  refine ⟨eta, heta, ⋃ i ∈ s, V i, isOpen_biUnion (fun i _ => (hh i).2.1), hcover,
    (fun r => ∑ i ∈ s, phi i r), desingularizer_sum s hs phi hphi, ?_⟩
  intro x hx r hxr hr hre v hv
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have hk := (hh i).2.2.2 x hxi
  have hlo : h i < h x := by rw [hl i i.2, hxr]; exact_mod_cast (by linarith : l < l+r)
  have hhi : h x < h i + (radius i : EReal) := by
    rw [hl i i.2, hxr, ← EReal.coe_add]
    exact_mod_cast (by linarith [he i hi] : l+r < l+radius i)
  have hhkl := hk hlo hhi v hv
  have hid : (h x-h i).toReal = r := by
    rw [hxr, hl i i.2, ← EReal.coe_sub, EReal.toReal_coe]; ring
  rw [hid] at hhkl
  have hd : deriv (phi i) r ≤ deriv (fun r => ∑ j ∈ s, phi j r) r := by
    rw [deriv_fun_sum (fun j hj => desingularizer_differentiable (hphi j hj) ⟨hr,hre⟩)]
    exact Finset.single_le_sum (fun j hj => ((hphi j hj).2.2.2.2.2 r ⟨hr,hre⟩).le) hi
  exact hhkl.trans (mul_le_mul_of_nonneg_right hd (norm_nonneg _))
end FracPSG.Abstract.Fresh
end

section

open Filter Topology

namespace FracPSG.Abstract.Fresh

variable {P : ℕ} {z : ℕ → EuclideanSpace ℝ (Fin P)}

theorem cluster_closed : IsClosed (clusterSet z) :=
  isClosed_setOfPred_clusterPt

theorem cluster_subset_closure : clusterSet z ⊆ closure (Set.range z) := by
  intro x hx
  exact isClosed_closure.mem_of_mapClusterPt hx
    (Eventually.of_forall fun n => subset_closure (Set.mem_range_self n))

theorem cluster_compact (hb : Bornology.IsBounded (Set.range z)) :
    IsCompact (clusterSet z) :=
  hb.isCompact_closure.of_isClosed_subset cluster_closed cluster_subset_closure

theorem cluster_nonempty (hb : Bornology.IsBounded (Set.range z)) :
    (clusterSet z).Nonempty := by
  obtain ⟨x, _, hx⟩ := hb.isCompact_closure.exists_mapClusterPt (f := atTop) (u := z)
    (Filter.tendsto_principal.mpr (Filter.Eventually.of_forall fun n =>
      subset_closure (Set.mem_range_self n)))
  exact ⟨x, hx⟩

theorem eventually_mem_of_cluster_subset (hb : Bornology.IsBounded (Set.range z))
    {U : Set (EuclideanSpace ℝ (Fin P))} (hU : IsOpen U)
    (hs : clusterSet z ⊆ U) : ∀ᶠ n in atTop, z n ∈ U := by
  by_contra hn
  have hf : ∃ᶠ n in atTop, z n ∈ closure (Set.range z) ∩ Uᶜ := by
    simpa only [Set.mem_inter_iff, show ∀ n, z n ∈ closure (Set.range z) from
      fun n => subset_closure (Set.mem_range_self n), true_and, Set.mem_compl_iff]
      using (Filter.not_eventually.mp hn)
  obtain ⟨x, hx, hc⟩ :=
    (hb.isCompact_closure.inter_right hU.isClosed_compl).exists_mapClusterPt_of_frequently hf
  exact hx.2 (hs hc)

end FracPSG.Abstract.Fresh
end

section
open Filter Topology
namespace FracPSG.Abstract.Fresh

theorem square_sum_bound (r d : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hr : ∀ n, 0 ≤ r n) (hd : ∀ n, a * d n ^ 2 ≤ r n - r (n+1)) (m : ℕ) :
    (∑ n ∈ Finset.range m, d n ^ 2) ≤ r 0 / a := by
  have hh : a * (∑ n ∈ Finset.range m, d n ^ 2) ≤ r 0 - r m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, mul_add]
      linarith [hd m]
  apply (le_div_iff₀ ha).2
  nlinarith [hr m]

theorem square_summable (r d : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hr : ∀ n, 0 ≤ r n) (hd : ∀ n, a * d n ^ 2 ≤ r n - r (n+1)) :
    Summable (fun n => d n ^ 2) :=
  summable_of_sum_range_le (fun n => sq_nonneg (d n)) (square_sum_bound r d a ha hr hd)

theorem steps_bounded (r d : ℕ → ℝ) (a : ℝ) (ha : 0 < a)
    (hr : ∀ n, 0 ≤ r n) (hd : ∀ n, a * d n ^ 2 ≤ r n - r (n+1)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, d n ≤ B := by
  refine ⟨Real.sqrt (r 0 / a), Real.sqrt_nonneg _, ?_⟩
  intro n
  have hs := square_sum_bound r d a ha hr hd (n+1)
  have hn : d n ^ 2 ≤ ∑ i ∈ Finset.range (n+1), d i ^ 2 :=
    Finset.single_le_sum (fun i _ => sq_nonneg (d i)) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  exact Real.le_sqrt_of_sq_le (le_trans hn hs)
end FracPSG.Abstract.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace FracPSG.Abstract.Fresh

lemma signed_shift_summable (Δ : ℤ → ℝ)
    (h : Summable (fun n : ℕ => Δ n)) (j : ℤ) :
    Summable (fun n : ℕ => Δ ((n : ℤ) + j)) := by
  let K := j.natAbs
  let d := ((K : ℤ) + j).toNat
  have hj : -(j.natAbs : ℤ) ≤ j := by
    simpa only [Int.natCast_natAbs] using neg_abs_le j
  have hd : 0 ≤ (K : ℤ) + j := by dsimp [K]; omega
  have he : (fun n : ℕ => Δ (((n + K : ℕ) : ℤ) + j)) =
      (fun n : ℕ => Δ ((n + d : ℕ) : ℤ)) := by
    funext n
    congr 1
    dsimp [d]
    omega
  apply (summable_nat_add_iff K).mp
  rw [he]
  exact (summable_nat_add_iff d).mpr h

lemma shifted_prefix_bound (Δ : ℤ → ℝ) (B : ℝ)
    (h0 : ∀ z, 0 ≤ Δ z) (hneg : ∀ z < 0, Δ z = 0)
    (hB : ∀ z, Δ z ≤ B) (M : ℕ) (i : ℤ) :
    (∑ n ∈ Finset.range M, Δ ((n : ℤ) - i)) ≤
      (∑ n ∈ Finset.range M, Δ n) + (i.natAbs : ℝ) * B := by
  classical
  let S : Finset ℕ := (Finset.range M).filter (fun n : ℕ => 0 ≤ (n : ℤ) - i)
  let f : ℕ → ℕ := fun n => ((n : ℤ) - i).toNat
  have hfilt : (∑ n ∈ S, Δ ((n : ℤ) - i)) =
      ∑ n ∈ Finset.range M, Δ ((n : ℤ) - i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hns
    apply hneg
    have hh : ¬ 0 ≤ (n : ℤ) - i := by
      intro h
      exact hns (Finset.mem_filter.mpr ⟨hn, h⟩)
    omega
  have hinj : Set.InjOn f (↑S : Set ℕ) := by
    intro a ha b hb he
    have ha0 := (Finset.mem_filter.mp ha).2
    have hb0 := (Finset.mem_filter.mp hb).2
    dsimp [f] at he
    omega
  have himg : (∑ z ∈ S.image f, Δ (z : ℤ)) = ∑ n ∈ S, Δ ((n : ℤ) - i) := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 := (Finset.mem_filter.mp hn).2
    congr 1
    dsimp [f]
    omega
  have hsub : S.image f ⊆ Finset.range (M + i.natAbs) := by
    intro z hz
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hz
    have hnM := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hn0 := (Finset.mem_filter.mp hn).2
    have hi : -(i.natAbs : ℤ) ≤ i := by
      simpa only [Int.natCast_natAbs] using neg_abs_le i
    apply Finset.mem_range.mpr
    dsimp [f]
    omega
  have hsum : (∑ n ∈ Finset.range M, Δ ((n : ℤ) - i)) ≤
      ∑ n ∈ Finset.range (M + i.natAbs), Δ (n : ℤ) := by
    rw [← hfilt, ← himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => h0 n)
  have htail : (∑ n ∈ Finset.range i.natAbs, Δ ((M + n : ℕ) : ℤ)) ≤
      (i.natAbs : ℝ) * B := by
    calc
      _ ≤ ∑ _n ∈ Finset.range i.natAbs, B := Finset.sum_le_sum (fun n _ => hB _)
      _ = _ := by simp
  rw [Finset.sum_range_add] at hsum
  linarith

end FracPSG.Abstract.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace FracPSG.Abstract.Fresh

lemma weighted_shifted_prefix_bound (Δ : ℤ → ℝ) (B : ℝ)
    (h0 : ∀ z, 0 ≤ Δ z) (hneg : ∀ z < 0, Δ z = 0) (hB : ∀ z, Δ z ≤ B)
    (S : Finset ℤ) (lam : ℤ → ℝ) (hlam : ∀ i ∈ S, 0 ≤ lam i)
    (hs : ∑ i ∈ S, lam i = 1) (M : ℕ) :
    (∑ n ∈ Finset.range M, ∑ i ∈ S, lam i * Δ ((n : ℤ) - i)) ≤
      (∑ n ∈ Finset.range M, Δ n) +
        ∑ i ∈ S, lam i * ((i.natAbs : ℝ) * B) := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ i ∈ S, lam i * ((∑ n ∈ Finset.range M, Δ n) + (i.natAbs : ℝ) * B) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (shifted_prefix_bound Δ B h0 hneg hB M i) (hlam i hi)
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hs, one_mul]

lemma summable_of_global_delayed_recurrence (Δ : ℤ → ℝ) (B C : ℝ)
    (h0 : ∀ z, 0 ≤ Δ z) (hneg : ∀ z < 0, Δ z = 0) (hB : ∀ z, Δ z ≤ B)
    (hC : 0 ≤ C) (ψ ε : ℕ → ℝ) (hψ : ∀ n, 0 ≤ ψ n) (hε : ∀ n, 0 ≤ ε n)
    (hεsum : Summable ε) (S : Finset ℤ) (lam : ℤ → ℝ)
    (hlam : ∀ i ∈ S, 0 ≤ lam i) (hs : ∑ i ∈ S, lam i = 1)
    (hrec : ∀ n : ℕ, 2 * Δ n ≤ C * (ψ n - ψ (n + 1)) +
      (∑ i ∈ S, lam i * Δ ((n : ℤ) - i)) + ε n) :
    Summable (fun n : ℕ => Δ n) := by
  apply summable_of_sum_range_le (fun n => h0 n)
    (c := C * ψ 0 + (∑ i ∈ S, lam i * ((i.natAbs : ℝ) * B)) + ∑' n, ε n)
  intro M
  have hsum := Finset.sum_le_sum (s := Finset.range M) (fun n _ => hrec n)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_sub'] at hsum
  have hdelay := weighted_shifted_prefix_bound Δ B h0 hneg hB S lam hlam hs M
  have herr := hεsum.sum_le_tsum (Finset.range M) (fun n _ => hε n)
  have hdrop : C * (ψ 0 - ψ M) ≤ C * ψ 0 := by
    nlinarith [mul_nonneg hC (hψ M)]
  linarith

lemma summable_of_eventual_delayed_recurrence (Δ : ℤ → ℝ) (B C : ℝ)
    (h0 : ∀ z, 0 ≤ Δ z) (hneg : ∀ z < 0, Δ z = 0) (hB : ∀ z, Δ z ≤ B)
    (hC : 0 ≤ C) (ψ ε : ℕ → ℝ) (hψ : ∀ n, 0 ≤ ψ n) (hε : ∀ n, 0 ≤ ε n)
    (hεsum : Summable ε) (S : Finset ℤ) (lam : ℤ → ℝ)
    (hlam : ∀ i ∈ S, 0 ≤ lam i) (hs : ∑ i ∈ S, lam i = 1)
    (hrec : ∀ᶠ n : ℕ in Filter.atTop, 2 * Δ n ≤ C * (ψ n - ψ (n + 1)) +
      (∑ i ∈ S, lam i * Δ ((n : ℤ) - i)) + ε n) :
    Summable (fun n : ℕ => Δ n) := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hrec
  let g : ℕ → ℝ := fun n => if n < N then 2 * Δ n + C * ψ (n + 1) else 0
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    dsimp [g]
    split_ifs
    · exact add_nonneg (mul_nonneg (by norm_num) (h0 n)) (mul_nonneg hC (hψ (n + 1)))
    · exact le_rfl
  have hgsum : Summable g := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    have hn' : ¬n < N := by simpa using hn
    simp [g, hn']
  apply summable_of_global_delayed_recurrence Δ B C h0 hneg hB hC ψ
    (fun n => ε n + g n) hψ (fun n => add_nonneg (hε n) (hg0 n))
    (hεsum.add hgsum) S lam hlam hs
  intro n
  by_cases hn : n < N
  · have hdel : 0 ≤ ∑ i ∈ S, lam i * Δ ((n : ℤ) - i) :=
      Finset.sum_nonneg (fun i hi => mul_nonneg (hlam i hi) (h0 _))
    have hpos := mul_nonneg hC (hψ n)
    dsimp [g]
    rw [if_pos hn]
    nlinarith [hε n]
  · simpa [g, hn] using hN n (by omega)

end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh

theorem native_finite_length {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ}
    {ilo ihi : ℤ} {lam : ℤ → ℝ}
    (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam) (h3 : H3 h z)
    (h4 : H4 α β ε) (hb : Bornology.IsBounded (Set.range z))
    (hc : ∀ x ∈ clusterSet z, ∀ y ∈ clusterSet z, h x = h y)
    (hk : ∀ x ∈ clusterSet z, HasKLProperty h x) : Summable (fun n : ℕ => Δ n) := by
  obtain ⟨l, hrl, _, hcl, hlo⟩ := uniform_value_limit hs h1 h2 h3 hc
  let r : ℕ → ℝ := fun n => (h (z n)).toReal-l
  have hr : ∀ n, 0 ≤ r n := fun n => sub_nonneg.mpr (hlo n)
  have hrt : Tendsto r atTop (𝓝 0) := by simpa [r] using hrl.sub_const l
  obtain ⟨a, ha, hal⟩ := h4.1
  obtain ⟨g, hg, hgl⟩ := h4.2.1
  have hdec : ∀ n : ℕ, a * (Δ n)^2 ≤ r n-r (n+1) := by
    intro n
    exact (mul_le_mul_of_nonneg_right (hal n) (sq_nonneg _)).trans (gap_decrease hs h1 h2 l n)
  obtain ⟨B, hB0, hB⟩ := steps_bounded r (fun n => Δ n) a ha hr hdec
  have hBz : ∀ j : ℤ, Δ j ≤ B := by
    intro j
    by_cases hj : 0 ≤ j
    · simpa only [Int.toNat_of_nonneg hj] using hB j.toNat
    · rw [hs.delta_neg j (lt_of_not_ge hj)]; exact hB0
  obtain ⟨eta, heta, U, hU, hcover, φ, hφ, hineq⟩ :=
    uniform_kl (cluster_compact hb) (cluster_nonempty hb) hcl hk
  let ψ : ℕ → ℝ := fun n => max 0 (φ (r n))
  apply summable_of_eventual_delayed_recurrence Δ B (1/g) hs.delta_nonneg hs.delta_neg hBz
    (by positivity) ψ ε (fun n => le_max_left _ _) hs.eps_nonneg h4.2.2
    (Finset.Icc ilo ihi) lam hs.lam_nonneg hs.lam_sum
  filter_upwards [eventually_mem_of_cluster_subset hb hU hcover, hrt.eventually_lt_const heta] with n hn hsmall
  have hsr : r (n+1) ≤ r n := sub_le_sub_right (real_values_antitone hs h1 h2 (Nat.le_succ n)) l
  have hψn : ψ n = φ (r n) := max_eq_right (hφ.2.2.1 _ ⟨hr n,hsmall⟩)
  have hψs : ψ (n+1) = φ (r (n+1)) := max_eq_right (hφ.2.2.1 _ ⟨hr _,hsr.trans_lt hsmall⟩)
  rw [hψn,hψs]
  have hh := native_recurrence hs h1 h2 hg hlo hφ n hsmall (hgl n) (by
    intro hp v hv
    apply hineq (z n) hn (r n) ?_ hp hsmall v hv
    change h (z n) = ((l + ((h (z n)).toReal-l) : ℝ) : EReal)
    rw [show l + ((h (z n)).toReal-l) = (h (z n)).toReal by ring]
    exact (value_coe hs h2 n).symm)
  simpa only [one_div_mul_eq_div] using hh
end FracPSG.Abstract.Fresh
end

section

open Filter Topology
open NonconvexSplitting.Shared

namespace FracPSG.Abstract.Fresh

variable {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}

def regularTriples (h : EuclideanSpace ℝ (Fin P) → EReal) :
    Set (EuclideanSpace ℝ (Fin P) × EuclideanSpace ℝ (Fin P) × ℝ) :=
  {q | IsRegularSubgrad h q.1 q.2.1 ∧ h q.1 = (q.2.2 : EReal)}

theorem limitingSubdiff_iff_closure (hbot : ∀ y, h y ≠ ⊥)
    {x v : EuclideanSpace ℝ (Fin P)} (hx : h x ≠ ⊤) :
    v ∈ LimitingSubdiff h x ↔ (x, v, (h x).toReal) ∈ closure (regularTriples h) := by
  constructor
  · rintro ⟨_, xs, vs, hxs, hval, hvs, hreg⟩
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun n => (xs n, vs n, (h (xs n)).toReal), ?_, ?_⟩
    · intro n
      exact ⟨hreg n, (EReal.coe_toReal (hreg n).1 (hbot _)).symm⟩
    · exact hxs.prodMk_nhds (hvs.prodMk_nhds ((EReal.tendsto_toReal hx (hbot x)).comp hval))
  · intro hc
    obtain ⟨q, hq, ht⟩ := mem_closure_iff_seq_limit.mp hc
    refine ⟨hx, fun n => (q n).1, fun n => (q n).2.1, ht.fst_nhds, ?_, ht.snd_nhds.fst_nhds, ?_⟩
    · have hv := EReal.tendsto_coe.mpr ht.snd_nhds.snd_nhds
      have he : (fun n => h (q n).1) = (fun n => ((q n).2.2 : EReal)) :=
        funext fun n => (hq n).2
      rw [he]
      simpa only [EReal.coe_toReal hx (hbot x)] using hv
    · exact fun n => (hq n).1

theorem limitingSubdiff_attentive_closed (hbot : ∀ y, h y ≠ ⊥)
    {x v : EuclideanSpace ℝ (Fin P)} (hx : h x ≠ ⊤)
    {xs vs : ℕ → EuclideanSpace ℝ (Fin P)}
    (hxs : Tendsto xs atTop (𝓝 x))
    (hval : Tendsto (fun n => h (xs n)) atTop (𝓝 (h x)))
    (hvs : Tendsto vs atTop (𝓝 v))
    (hmem : ∀ n, vs n ∈ LimitingSubdiff h (xs n)) :
    v ∈ LimitingSubdiff h x := by
  apply (limitingSubdiff_iff_closure hbot hx).mpr
  apply isClosed_closure.mem_of_tendsto
    (hxs.prodMk_nhds (hvs.prodMk_nhds ((EReal.tendsto_toReal hx (hbot x)).comp hval)))
  exact Eventually.of_forall fun n =>
    (limitingSubdiff_iff_closure hbot (hmem n).1).mp (hmem n)

end FracPSG.Abstract.Fresh
end

section

open Filter Topology
open NonconvexSplitting.Shared

namespace FracPSG.Abstract.Fresh

variable {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
variable {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ}
variable {ilo ihi : ℤ} {lam : ℤ → ℝ}

theorem stationarity_of_shift_summable
    (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h2 : H2 h z β ε Δ ilo ihi lam) (he : Summable ε)
    (hd : ∀ j : ℤ, Summable (fun n : ℕ => Δ ((n : ℤ) + j)))
    (hb : ∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ β n)
    {zt : EuclideanSpace ℝ (Fin P)} (hz : zt ∈ omega0 h z)
    (ht : h zt ≠ ⊤) : (0 : EuclideanSpace ℝ (Fin P)) ∈ LimitingSubdiff h zt := by
  classical
  choose v hv hbound using h2
  obtain ⟨b, hb, hbβ⟩ := hb
  have hW : Tendsto (fun n : ℕ => ∑ i ∈ Finset.Icc ilo ihi,
      lam i * Δ ((n : ℤ) - i)) atTop (𝓝 0) := by
    have hh := tendsto_finsetSum (Finset.Icc ilo ihi)
      (fun i _ => (hd (-i)).tendsto_atTop_zero.const_mul (lam i))
    simpa only [sub_eq_add_neg, mul_zero, Finset.sum_const_zero] using hh
  have hu : Tendsto (fun n : ℕ =>
      ((∑ i ∈ Finset.Icc ilo ihi, lam i * Δ ((n : ℤ) - i)) + ε n) / b)
      atTop (𝓝 0) := by
    simpa using (hW.add he.tendsto_atTop_zero).div_const b
  have hn : Tendsto (fun n => ‖v n‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => norm_nonneg _) _ hu
    intro n
    apply (le_div_iff₀ hb).mpr
    calc
      ‖v n‖ * b = b * ‖v n‖ := mul_comm _ _
      _ ≤ β n * ‖v n‖ := mul_le_mul_of_nonneg_right (hbβ n) (norm_nonneg _)
      _ ≤ _ := hbound n
  have hvt : Tendsto v atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  obtain ⟨k, hk, hzk⟩ := hz.1.tendsto_subseq
  exact limitingSubdiff_attentive_closed hs.proper.1 ht hzk
    (hz.2.comp hk.tendsto_atTop) (hvt.comp hk.tendsto_atTop) (fun n => hv (k n))

end FracPSG.Abstract.Fresh
end

section

open Filter Topology

namespace FracPSG.Abstract.Fresh

theorem strong_limit_of_summable_steps {H : Type*} [NormedAddCommGroup H]
    [CompleteSpace H] (x : ℕ → H)
    (hs : Summable (fun n => ‖x (n + 1) - x n‖)) :
    ∃ z, Tendsto x atTop (𝓝 z) := by
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_summable_dist
  simpa only [dist_eq_norm, norm_sub_rev] using hs

theorem h5_convergence {H : Type*} [NormedAddCommGroup H] [CompleteSpace H]
    {x : ℕ → H} {Δ : ℤ → ℝ} (hd : ∀ i, 0 ≤ Δ i)
    (hshift : ∀ j : ℤ, Summable (fun n : ℕ => Δ ((n : ℤ) + j)))
    (hx : H5 x Δ) : Summable (fun n => ‖x (n + 1) - x n‖) ∧
      ∃ z, Tendsto x atTop (𝓝 z) := by
  obtain ⟨j, c, hc⟩ := hx
  have hs : Summable (fun n => ‖x (n + 1) - x n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _
      ((hshift j).mul_left (max c 0))
    intro n
    exact (hc n).trans (mul_le_mul_of_nonneg_right (le_max_left c 0) (hd _))
  exact ⟨hs, strong_limit_of_summable_steps x hs⟩

end FracPSG.Abstract.Fresh
end

section

open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

namespace FracPSG.Abstract.Fresh

variable {N P : ℕ} {x : ℕ → EuclideanSpace ℝ (Fin N)}
variable {h : EuclideanSpace ℝ (Fin P) → EReal} {z : ℕ → EuclideanSpace ℝ (Fin P)}
variable {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ} {lam : ℤ → ℝ}

theorem native_convergence (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (hd : Summable (fun n : ℕ => Δ n)) (hx : H5 x Δ) :
    Summable (fun n => ‖x (n + 1) - x n‖) ∧
      ∃ xb, Tendsto x atTop (𝓝 xb) :=
  h5_convergence hs.delta_nonneg (signed_shift_summable Δ hd) hx

theorem native_stationarity (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam)
    (he : Summable ε) (hd : Summable (fun n : ℕ => Δ n))
    (hb : ∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ β n)
    {zt : EuclideanSpace ℝ (Fin P)} (hz : zt ∈ omega0 h z) :
    (0 : EuclideanSpace ℝ (Fin P)) ∈ LimitingSubdiff h zt := by
  have hle : h zt ≤ h (z 0) := le_of_tendsto hz.2 (Eventually.of_forall
    fun n => values_antitone hs h1 (Nat.zero_le n))
  have ht : h zt ≠ ⊤ := ne_top_of_le_ne_top (value_finite hs h2 0).1 hle
  exact stationarity_of_shift_summable hs h2 he (signed_shift_summable Δ hd) hb hz ht

end FracPSG.Abstract.Fresh
end

section

open Filter Topology

namespace FracPSG.Abstract.Fresh

theorem signed_geometric_bound {Δ : ℤ → ℝ} {D r : ℝ}
    (hD : 0 ≤ D) (hr : 0 < r) (hn : ∀ i < 0, Δ i = 0)
    (hd : ∀ n : ℕ, Δ n ≤ D * r ^ n) (j : ℤ) (n : ℕ) :
    Δ ((n : ℤ) + j) ≤ (D * r ^ j) * r ^ n := by
  by_cases hk : 0 ≤ (n : ℤ) + j
  · have hh := hd (((n : ℤ) + j).toNat)
    rw [Int.toNat_of_nonneg hk] at hh
    have hp : r ^ (((n : ℤ) + j).toNat) = r ^ n * r ^ j := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hk, zpow_add₀ hr.ne', zpow_natCast]
    rw [hp] at hh
    nlinarith [hh]
  · rw [hn _ (lt_of_not_ge hk)]
    positivity

theorem h5_geometric_convergence {H : Type*} [NormedAddCommGroup H] [CompleteSpace H]
    {x : ℕ → H} {Δ : ℤ → ℝ} {D r : ℝ}
    (hD : 0 ≤ D) (hr : 0 < r) (hr1 : r < 1)
    (hn : ∀ i < 0, Δ i = 0) (hd : ∀ n : ℕ, Δ n ≤ D * r ^ n)
    (hx : H5 x Δ) (h0 : ∀ i, 0 ≤ Δ i) :
    ∃ xb : H, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖x n - xb‖ ≤ C * r ^ n := by
  obtain ⟨j, c, hc⟩ := hx
  let B := max c 0 * (D * r ^ j)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hstep : ∀ n, dist (x n) (x (n + 1)) ≤ B * r ^ n := by
    intro n
    rw [dist_eq_norm, norm_sub_rev]
    calc
      ‖x (n+1) - x n‖ ≤ c * Δ ((n : ℤ) + j) := hc n
      _ ≤ max c 0 * Δ ((n : ℤ) + j) :=
        mul_le_mul_of_nonneg_right (le_max_left c 0) (h0 _)
      _ ≤ max c 0 * ((D * r ^ j) * r ^ n) :=
        mul_le_mul_of_nonneg_left (signed_geometric_bound hD hr hn hd j n) (le_max_right c 0)
      _ = B * r ^ n := by dsimp [B]; ring
  obtain ⟨xb, hxb⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric r B hr1 hstep)
  have hden : 0 < 1-r := sub_pos.mpr hr1
  refine ⟨xb, B / (1-r) + 1, by positivity, ?_⟩
  intro n
  have hh := dist_le_of_le_geometric_of_tendsto r B hr1 hstep hxb n
  rw [dist_eq_norm] at hh
  calc
    ‖x n - xb‖ ≤ B * r ^ n / (1-r) := hh
    _ ≤ (B / (1-r) + 1) * r ^ n := by
      have hp := pow_nonneg hr.le n
      nlinarith [show B * r ^ n / (1-r) = (B / (1-r)) * r ^ n by ring]

end FracPSG.Abstract.Fresh
end

section

noncomputable section
namespace FracPSG.Abstract.Fresh

lemma square_descent_geometric_bound (v d : ℕ → ℝ) (a γ ρ : ℝ)
    (ha : 0 < a) (hγ : 0 < γ) (hρ : 0 ≤ ρ)
    (hv0 : ∀ n, 0 ≤ v n) (_hd0 : ∀ n, 0 ≤ d n)
    (hdesc : ∀ n, a * (d n) ^ 2 ≤ v n - v (n + 1))
    (hval : ∀ n, v n ≤ γ * ρ ^ n) :
    ∀ n, d n ≤ Real.sqrt (γ / a) * (Real.sqrt ρ) ^ n := by
  intro n
  have hdiv : 0 ≤ γ / a := le_of_lt (div_pos hγ ha)
  have hpow : ((Real.sqrt ρ) ^ n) ^ 2 = ρ ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, Real.sq_sqrt hρ]
  have hs : (Real.sqrt (γ / a) * (Real.sqrt ρ) ^ n) ^ 2 = (γ / a) * ρ ^ n := by
    rw [mul_pow, Real.sq_sqrt hdiv, hpow]
  have he : a * (Real.sqrt (γ / a) * (Real.sqrt ρ) ^ n) ^ 2 = γ * ρ ^ n := by
    rw [hs]
    field_simp [ha.ne']
  have ht : a * (d n) ^ 2 ≤ γ * ρ ^ n := by
    linarith [hdesc n, hval n, hv0 (n + 1)]
  have hsq : (d n) ^ 2 ≤ (Real.sqrt (γ / a) * (Real.sqrt ρ) ^ n) ^ 2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [he]
    exact ht
  have hb : 0 ≤ Real.sqrt (γ / a) * (Real.sqrt ρ) ^ n := by positivity
  nlinarith [_hd0 n]

lemma sqrt_geometric_rpow (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) :
    (Real.sqrt ρ) ^ n = ρ ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hρ]
  congr 1
  ring

lemma sqrt_ratio_positive (γ a : ℝ) (hγ : 0 < γ) (ha : 0 < a) :
    0 < Real.sqrt (γ / a) := Real.sqrt_pos.mpr (div_pos hγ ha)

end FracPSG.Abstract.Fresh
end

section

open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

namespace FracPSG.Abstract.Fresh

variable {N P : ℕ} {x : ℕ → EuclideanSpace ℝ (Fin N)}
variable {h : EuclideanSpace ℝ (Fin P) → EReal} {z : ℕ → EuclideanSpace ℝ (Fin P)}
variable {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ} {lam : ℤ → ℝ}

theorem native_iterate_rate (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam)
    (ha : ∃ a : ℝ, 0 < a ∧ ∀ n, a ≤ α n)
    (l γ ρ : ℝ) (hl : ∀ n, l ≤ (h (z n)).toReal)
    (hγ : 0 < γ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hval : ∀ n, (h (z n)).toReal-l ≤ γ * ρ ^ n) (hx : H5 x Δ) :
    ∃ xb : EuclideanSpace ℝ (Fin N), ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, ‖x n - xb‖ ≤ C * ρ ^ ((n : ℝ) / 2) := by
  obtain ⟨a, ha, haα⟩ := ha
  have hd : ∀ n : ℕ, a * Δ n ^ 2 ≤
      ((h (z n)).toReal-l) - ((h (z (n+1))).toReal-l) := by
    intro n
    exact (mul_le_mul_of_nonneg_right (haα n) (sq_nonneg _)).trans
      (gap_decrease hs h1 h2 l n)
  have hg := square_descent_geometric_bound (fun n => (h (z n)).toReal-l)
    (fun n => Δ n) a γ ρ ha hγ hρ.le
    (fun n => sub_nonneg.mpr (hl n)) (fun n => hs.delta_nonneg n) hd hval
  have hr : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hr1 : Real.sqrt ρ < 1 := by
    nlinarith [Real.sq_sqrt hρ.le, Real.sqrt_nonneg ρ]
  obtain ⟨xb, C, hC, hb⟩ := h5_geometric_convergence
    (Real.sqrt_nonneg (γ/a)) hr hr1 hs.delta_neg hg hx hs.delta_nonneg
  refine ⟨xb, C, hC, ?_⟩
  intro n
  simpa only [sqrt_geometric_rpow ρ hρ.le n] using hb n

end FracPSG.Abstract.Fresh
end

section

open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

namespace FracPSG.Abstract.Fresh

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem power_desingularizer_deriv {γ a r : ℝ} (hr : 0 < r) :
    deriv (fun s : ℝ => γ * s ^ (1-a)) r = γ * (1-a) * r ^ (-a) := by
  have hh := (Real.hasDerivAt_rpow_const (p := 1-a) (Or.inl hr.ne')).const_mul γ
  rw [hh.deriv]
  rw [show 1-a-1 = -a by ring]
  ring

theorem uniform_exponent_kl {h : K → EReal} {Ω : Set K} {l a : ℝ}
    (hc : IsCompact Ω) (hne : Ω.Nonempty) (hl : ∀ x ∈ Ω, h x = (l : EReal))
    (hkl : ∀ x ∈ Ω, HasKLPropertyExp h x a) :
    0 ≤ a ∧ a < 1 ∧ ∃ η : ℝ, 0 < η ∧ ∃ U : Set K,
      IsOpen U ∧ Ω ⊆ U ∧ ∃ Γ : ℝ, 0 < Γ ∧
      ∀ x ∈ U, ∀ r : ℝ, h x = ((l+r : ℝ) : EReal) → 0 < r → r < η →
        ∀ v ∈ LimitingSubdiff h x, 1 ≤ Γ * (1-a) * r ^ (-a) * ‖v‖ := by
  classical
  obtain ⟨x0, hx0⟩ := hne
  have ha := (hkl x0 hx0).1
  have ha1 := (hkl x0 hx0).2.1
  choose radius hr W hW gamma hg hineq using fun i : Ω => (hkl i i.2).2.2
  let V : Ω → Set K := fun i => interior (W i)
  have hopen : ∀ i, IsOpen (V i) := fun _ => isOpen_interior
  have hcover : Ω ⊆ ⋃ i : Ω, V i := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hW ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover V hopen hcover
  have hsne : s.Nonempty := by
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (hs hx0)
    exact ⟨i, hi⟩
  let η := s.inf' hsne radius
  have heta : 0 < η := (Finset.lt_inf'_iff hsne).mpr fun i _ => hr i
  have he : ∀ i ∈ s, η ≤ radius i := fun i hi => Finset.inf'_le radius hi
  let Γ := ∑ i ∈ s, gamma i
  have hΓ : 0 < Γ := Finset.sum_pos (fun i _ => hg i) hsne
  refine ⟨ha, ha1, η, heta, ⋃ i ∈ s, V i,
    isOpen_biUnion (fun i _ => hopen i), hs, Γ, hΓ, ?_⟩
  intro x hx r hxr hr0 hre v hv
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
  have hlo : h i < h x := by
    rw [hl i i.2, hxr]
    exact_mod_cast (by linarith : l < l+r)
  have hhi : h x < h i + (radius i : EReal) := by
    rw [hl i i.2, hxr, ← EReal.coe_add]
    exact_mod_cast (by linarith [he i hi] : l+r < l+radius i)
  have hh := hineq i x (interior_subset hxi) hlo hhi v hv
  have hid : (h x-h i).toReal = r := by
    rw [hxr, hl i i.2, ← EReal.coe_sub, EReal.toReal_coe]
    ring
  rw [hid, power_desingularizer_deriv hr0] at hh
  have hgam : gamma i ≤ Γ := Finset.single_le_sum (fun j _ => (hg j).le) hi
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr0.le _)
  exact mul_le_mul_of_nonneg_right hgam (sub_nonneg.mpr ha1.le)

end FracPSG.Abstract.Fresh
end

section
namespace FracPSG.Abstract.Fresh

theorem exponent_to_drop {r D a C v B : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (ha : a ≤ 1/2) (hD : 0 ≤ D) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hkl : 1 ≤ C*r^(-a)*v) (hv : v ≤ B*Real.sqrt D) :
    r ≤ (C*B)^2*D := by
  have hp : 0 < r^a := Real.rpow_pos_of_pos hr _
  have hpow : r^a ≤ C*v := by
    rw [Real.rpow_neg hr.le] at hkl
    have hh := mul_le_mul_of_nonneg_right hkl hp.le
    field_simp [ne_of_gt hp] at hh
    nlinarith
  have hs : Real.sqrt r ≤ r^a := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 ha
  have hb : Real.sqrt r ≤ (C*B)*Real.sqrt D :=
    hs.trans (hpow.trans (by nlinarith))
  have hsR := Real.sq_sqrt hr.le
  have hsD := Real.sq_sqrt hD
  have hnon := mul_nonneg (mul_nonneg hC hB) (Real.sqrt_nonneg D)
  nlinarith [Real.sqrt_nonneg r]

theorem contraction_of_drop {u v C : ℝ} (hC : 0 < C)
    (h : v ≤ C*(u-v)) : v ≤ (C/(1+C))*u := by
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : 0 < 1+C)).2
  nlinarith
end FracPSG.Abstract.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace FracPSG.Abstract.Fresh

lemma geometric_bound_of_eventual_step (r : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hstep : ∀ᶠ n : ℕ in Filter.atTop, r (n + L) ≤ q * r n) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ n, r n ≤ γ * ρ ^ n := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hstep
  let ρ := Real.exp (Real.log q / (L : ℝ))
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hρ : 0 < ρ := Real.exp_pos _
  have hρ1 : ρ < 1 := by
    apply Real.exp_lt_one_iff.mpr
    exact div_neg_of_neg_of_pos (Real.log_neg hq0 hq1) hLr
  have hpow : ρ ^ L = q := by
    dsimp [ρ]
    rw [← Real.exp_nat_mul]
    have he : (L : ℝ) * (Real.log q / (L : ℝ)) = Real.log q := by field_simp
    rw [he, Real.exp_log hq0]
  let γ := 1 + ∑ i ∈ Finset.range (N + L), |r i / ρ ^ i|
  have hγ : 0 < γ := by
    have hh : 0 ≤ ∑ i ∈ Finset.range (N + L), |r i / ρ ^ i| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp [γ]
    linarith
  refine ⟨γ, hγ, ρ, hρ, hρ1, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < N + L
      · have ha : |r n / ρ ^ n| ≤ ∑ i ∈ Finset.range (N + L), |r i / ρ ^ i| :=
          Finset.single_le_sum (f := fun i => |r i / ρ ^ i|) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr hn)
        have hb : r n / ρ ^ n ≤ γ := by
          have hc := le_abs_self (r n / ρ ^ n)
          dsimp [γ]
          linarith
        exact (div_le_iff₀ (pow_pos hρ n)).mp hb
      · have hsub : N ≤ n - L := by omega
        have hlt : n - L < n := by omega
        have heq : n - L + L = n := by omega
        have hs := hN (n - L) hsub
        rw [heq] at hs
        calc
          r n ≤ q * r (n - L) := hs
          _ ≤ q * (γ * ρ ^ (n - L)) := mul_le_mul_of_nonneg_left (ih _ hlt) hq0.le
          _ = γ * ρ ^ (n - L) * ρ ^ L := by
            rw [← hpow]
            ring
          _ = γ * ρ ^ ((n - L) + L) := by
            rw [pow_add]
            ring
          _ = γ * ρ ^ n := by rw [heq]

end FracPSG.Abstract.Fresh
end

section

open Filter Topology

namespace FracPSG.Abstract.Fresh

theorem geometric_of_signed_contraction (r : ℕ → ℝ) (hr : Antitone r)
    (ilo ihi : ℤ) (hilo : ilo ≤ ihi) (hilo1 : ilo ≤ 1)
    (C : ℝ) (hC : 0 < C)
    (hstep : ∀ᶠ n : ℕ in atTop,
      r n ≤ C * (r ((n : ℤ) - ihi).toNat - r ((n : ℤ) + 1 - ilo).toNat)) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ n, r n ≤ γ * ρ ^ n := by
  let L := (ihi + 1 - ilo).toNat
  have hLi : 0 < ihi + 1 - ilo := by omega
  have hL : 0 < L := by dsimp [L]; omega
  let q := C / (1+C)
  have hden : 0 < 1+C := by linarith
  have hq : 0 < q := div_pos hC hden
  have hq1 : q < 1 := (div_lt_one hden).mpr (by linarith)
  apply geometric_bound_of_eventual_step r L hL q hq hq1
  obtain ⟨N, hN⟩ := eventually_atTop.mp hstep
  apply eventually_atTop.mpr
  refine ⟨N + ihi.natAbs, ?_⟩
  intro t ht
  let n := ((t : ℤ) + ihi).toNat
  have hab : -(ihi.natAbs : ℤ) ≤ ihi := by
    simpa only [Int.natCast_natAbs] using neg_abs_le ihi
  have hn0 : 0 ≤ (t : ℤ) + ihi := by omega
  have hni : (n : ℤ) = (t : ℤ) + ihi := by
    dsimp [n]
    exact Int.toNat_of_nonneg hn0
  have hnN : N ≤ n := by omega
  have hstart : ((n : ℤ) - ihi).toNat = t := by omega
  have hend : ((n : ℤ) + 1 - ilo).toNat = t + L := by
    dsimp [L]
    omega
  have hne : n ≤ t + L := by dsimp [L]; omega
  have hh := hN n hnN
  rw [hstart, hend] at hh
  have hm := hr hne
  have hh' : r (t+L) * (1+C) ≤ C * r t := by nlinarith
  have hdiv := (le_div_iff₀ hden).mpr hh'
  calc
    r (t+L) ≤ C * r t / (1+C) := hdiv
    _ = q * r t := by dsimp [q]; ring

end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh

theorem value_rate_of_relative {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ}
    {ilo ihi : ℤ} {lam : ℤ → ℝ}
    (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam) (h3 : H3 h z)
    (hb : Bornology.IsBounded (Set.range z))
    (hc : ∀ x ∈ clusterSet z, ∀ y ∈ clusterSet z, h x = h y)
    {a : ℝ} (ha : a ≤ 1/2) (hk : ∀ x ∈ clusterSet z, HasKLPropertyExp h x a)
    (hilo : ilo ≤ 1)
    (hbnd : ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      ∃ v ∈ LimitingSubdiff h (z n), ‖v‖ ≤ B * Real.sqrt
        ((h (z ((n:ℤ)-ihi).toNat)).toReal-(h (z ((n:ℤ)+1-ilo).toNat)).toReal)) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ x ∈ omega0 h z, ∀ n, (h (z n)).toReal-(h x).toReal ≤ γ*ρ^n := by
  obtain ⟨l, hrl, _, hcl, hlo⟩ := uniform_value_limit hs h1 h2 h3 hc
  let r : ℕ → ℝ := fun n => (h (z n)).toReal-l
  have hr : ∀ n, 0 ≤ r n := fun n => sub_nonneg.mpr (hlo n)
  have hrt : Tendsto r atTop (𝓝 0) := by simpa [r] using hrl.sub_const l
  have hanti : Antitone r := fun i j hij => sub_le_sub_right (real_values_antitone hs h1 h2 hij) l
  obtain ⟨_, ha1, eta, heta, U, hU, hcover, Γ, hΓ, hineq⟩ :=
    uniform_exponent_kl (cluster_compact hb) (cluster_nonempty hb) hcl hk
  obtain ⟨B, hB, hbound⟩ := hbnd
  let C := (Γ*(1-a)*B)^2+1
  have hC : 0 < C := by dsimp [C]; positivity
  have hstep : ∀ᶠ n : ℕ in atTop, r n ≤ C*(r ((n:ℤ)-ihi).toNat-r ((n:ℤ)+1-ilo).toNat) := by
    filter_upwards [hbound, eventually_mem_of_cluster_subset hb hU hcover,
      hrt.eventually_lt_const heta, hrt.eventually_lt_const (by norm_num : (0:ℝ)<1)] with n hn hnu hneta hn1
    obtain ⟨v, hv, hvb⟩ := hn
    let D := r ((n:ℤ)-ihi).toNat-r ((n:ℤ)+1-ilo).toNat
    have hD : 0 ≤ D := sub_nonneg.mpr (hanti (Int.toNat_le_toNat (by have := hs.ilo_le_ihi; omega)))
    have hvb' : ‖v‖ ≤ B*Real.sqrt D := by simpa only [D,r,sub_sub_sub_cancel_right] using hvb
    by_cases hp : 0 < r n
    · have hxval : h (z n) = ((l+r n : ℝ) : EReal) := by
        change h (z n) = ((l+((h (z n)).toReal-l) : ℝ) : EReal)
        rw [show l+((h (z n)).toReal-l) = (h (z n)).toReal by ring]
        exact (value_coe hs h2 n).symm
      have hki := hineq (z n) hnu (r n) hxval hp hneta v hv
      have hh := exponent_to_drop hp hn1.le ha hD (mul_nonneg hΓ.le (sub_nonneg.mpr ha1.le)) hB.le hki hvb'
      change r n ≤ C*D
      dsimp [C]
      nlinarith
    · have hz : r n=0 := le_antisymm (le_of_not_gt hp) (hr n)
      rw [hz]
      exact mul_nonneg hC.le hD
  obtain ⟨γ,hγ,ρ,hρ,hρ1,hval⟩ := geometric_of_signed_contraction r hanti ilo ihi hs.ilo_le_ihi hilo C hC hstep
  refine ⟨γ,hγ,ρ,hρ,hρ1,?_⟩
  intro x hx n
  rw [hcl x hx.1, EReal.toReal_coe]
  exact hval n
end FracPSG.Abstract.Fresh
end

section

noncomputable section
open scoped BigOperators
namespace FracPSG.Abstract.Fresh

lemma weighted_common_energy_bound {ι : Type*} (S : Finset ι)
    (lam x A : ι → ℝ) (β d E : ℝ) (hβ : 0 < β) (hd : 0 < d)
    (hlam : ∀ i ∈ S, 0 ≤ lam i) (hs : ∑ i ∈ S, lam i = 1)
    (hdesc : ∀ i ∈ S, A i * (x i) ^ 2 ≤ E)
    (hprod : ∀ i ∈ S, d ≤ A i * β ^ 2) :
    (∑ i ∈ S, lam i * x i) / β ≤ Real.sqrt (E / d) := by
  have hb (i : ι) (hi : i ∈ S) : x i / β ≤ Real.sqrt (E / d) := by
    have hp := mul_le_mul_of_nonneg_right (hprod i hi) (sq_nonneg (x i))
    have hh : d * (x i / β) ^ 2 ≤ A i * (x i) ^ 2 := by
      rw [div_pow, ← mul_div_assoc]
      apply (div_le_iff₀ (pow_pos hβ 2)).mpr
      nlinarith
    have hq : (x i / β) ^ 2 ≤ E / d := by
      apply (le_div_iff₀ hd).mpr
      nlinarith [hdesc i hi]
    exact Real.le_sqrt_of_sq_le hq
  calc
    (∑ i ∈ S, lam i * x i) / β = ∑ i ∈ S, lam i * (x i / β) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ S, lam i * Real.sqrt (E / d) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hb i hi) (hlam i hi)
    _ = Real.sqrt (E / d) := by rw [← Finset.sum_mul, hs, one_mul]

lemma signed_delayed_energy_bound (r α : ℕ → ℝ) (Δ : ℤ → ℝ)
    (hr : Antitone r) (ilo ihi : ℤ) (hio : ilo ≤ ihi)
    (lam : ℤ → ℝ) (hlam : ∀ i ∈ Finset.Icc ilo ihi, 0 ≤ lam i)
    (hs : ∑ i ∈ Finset.Icc ilo ihi, lam i = 1)
    (n : ℕ) (hn : ilo.natAbs + ihi.natAbs + 1 ≤ n)
    (β d : ℝ) (hβ : 0 < β) (hd : 0 < d)
    (hdesc : ∀ j : ℕ, α j * (Δ (j : ℤ)) ^ 2 ≤ r j - r (j + 1))
    (hprod : ∀ i ∈ Finset.Icc ilo ihi, d ≤ α (((n : ℤ) - i).toNat) * β ^ 2) :
    (∑ i ∈ Finset.Icc ilo ihi, lam i * Δ ((n : ℤ) - i)) / β ≤
      (1 / Real.sqrt d) * Real.sqrt (r (((n : ℤ) - ihi).toNat) -
        r (((n : ℤ) + 1 - ilo).toNat)) := by
  have hlo : ilo ≤ (ilo.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using le_abs_self ilo
  have hhi : ihi ≤ (ihi.natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs] using le_abs_self ihi
  have hstart : 0 ≤ (n : ℤ) - ihi := by omega
  have hend : 0 ≤ (n : ℤ) + 1 - ilo := by omega
  have hab : ((n : ℤ) - ihi).toNat ≤ ((n : ℤ) + 1 - ilo).toNat := by omega
  have hE : 0 ≤ r (((n : ℤ) - ihi).toNat) - r (((n : ℤ) + 1 - ilo).toNat) :=
    sub_nonneg.mpr (hr hab)
  have hlocal (i : ℤ) (hi : i ∈ Finset.Icc ilo ihi) :
      α (((n : ℤ) - i).toNat) * (Δ ((n : ℤ) - i)) ^ 2 ≤
        r (((n : ℤ) - ihi).toNat) - r (((n : ℤ) + 1 - ilo).toNat) := by
    have hii := Finset.mem_Icc.mp hi
    have hnonneg : 0 ≤ (n : ℤ) - i := by omega
    have hcast : ((((n : ℤ) - i).toNat : ℕ) : ℤ) = (n : ℤ) - i := by omega
    have ha : ((n : ℤ) - ihi).toNat ≤ ((n : ℤ) - i).toNat := by omega
    have hb : ((n : ℤ) - i).toNat + 1 ≤ ((n : ℤ) + 1 - ilo).toNat := by omega
    have hstep := hdesc (((n : ℤ) - i).toNat)
    rw [hcast] at hstep
    have hleft := hr ha
    have hright := hr hb
    linarith
  have h := weighted_common_energy_bound (Finset.Icc ilo ihi) lam
    (fun i => Δ ((n : ℤ) - i)) (fun i => α (((n : ℤ) - i).toNat)) β d
    (r (((n : ℤ) - ihi).toNat) - r (((n : ℤ) + 1 - ilo).toNat)) hβ hd hlam hs hlocal hprod
  rw [Real.sqrt_div hE] at h
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using h

end FracPSG.Abstract.Fresh
end

section
open Filter Topology
open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL
namespace FracPSG.Abstract.Fresh
variable {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
variable {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ}
variable {ilo ihi : ℤ} {lam : ℤ → ℝ}

theorem native_relative_bound (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam)
    {d : ℝ} (hd : DeltaLowerBound α β ilo ihi d)
    (herr : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ε n / β n ≤ C * Real.sqrt
      ((h (z ((n:ℤ)-ihi).toNat)).toReal-(h (z ((n:ℤ)+1-ilo).toNat)).toReal)) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ n : ℕ in atTop,
      ∃ v ∈ LimitingSubdiff h (z n), ‖v‖ ≤ B * Real.sqrt
        ((h (z ((n:ℤ)-ihi).toNat)).toReal-(h (z ((n:ℤ)+1-ilo).toNat)).toReal) := by
  obtain ⟨C,hC⟩ := herr
  have hdpos : 0 < d := hd.1
  refine ⟨1/Real.sqrt d + max C 0, add_pos_of_pos_of_nonneg (by positivity) (le_max_right _ _), ?_⟩
  filter_upwards [hC, eventually_ge_atTop (ilo.natAbs+ihi.natAbs+1)] with n hn hlarge
  obtain ⟨v,hv,herrv⟩ := h2 n
  refine ⟨v,hv,?_⟩
  have he := signed_delayed_energy_bound (fun j => (h (z j)).toReal) α Δ
    (real_values_antitone hs h1 h2) ilo ihi hs.ilo_le_ihi lam hs.lam_nonneg hs.lam_sum
    n hlarge (β n) d (hs.beta_pos n) hd.1
    (fun j => by linarith [value_decrease hs h1 h2 j]) (by
      intro i hi
      apply hd.2 n i hi
      have hii := (Finset.mem_Icc.mp hi).2
      have hh : ihi ≤ (ihi.natAbs : ℤ) := by simpa only [Int.natCast_natAbs] using le_abs_self ihi
      omega)
  have hvb : ‖v‖ ≤ (∑ i ∈ Finset.Icc ilo ihi, lam i*Δ ((n:ℤ)-i))/β n + ε n/β n := by
    rw [← add_div]
    apply (le_div_iff₀ (hs.beta_pos n)).2
    nlinarith [herrv]
  have hcmax := mul_le_mul_of_nonneg_right (le_max_left C 0)
    (Real.sqrt_nonneg ((h (z ((n:ℤ)-ihi).toNat)).toReal-(h (z ((n:ℤ)+1-ilo).toNat)).toReal))
  nlinarith

theorem native_value_rate (hs : AbstractSetting h α β ε Δ ilo ihi lam)
    (h1 : H1 h z α Δ) (h2 : H2 h z β ε Δ ilo ihi lam) (h3 : H3 h z)
    (hb : Bornology.IsBounded (Set.range z))
    (hc : ∀ x ∈ clusterSet z, ∀ y ∈ clusterSet z, h x = h y)
    {a : ℝ} (ha : a ≤ 1/2) (hk : ∀ x ∈ clusterSet z, HasKLPropertyExp h x a)
    (hilo : ilo ≤ 1) {d : ℝ} (hd : DeltaLowerBound α β ilo ihi d)
    (herr : ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ε n / β n ≤ C * Real.sqrt
      ((h (z ((n:ℤ)-ihi).toNat)).toReal-(h (z ((n:ℤ)+1-ilo).toNat)).toReal)) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ x ∈ omega0 h z, ∀ n, (h (z n)).toReal-(h x).toReal ≤ γ*ρ^n :=
  value_rate_of_relative hs h1 h2 h3 hb hc ha hk hilo (native_relative_bound hs h1 h2 hd herr)
end FracPSG.Abstract.Fresh
end

section

open Filter Topology

namespace FracPSG.Abstract.Fresh

open NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

/-- Theorem 5.2 (Abstract convergence; Boţ–Dao–Li, arXiv:2003.04124v2, p. 15). Under (H1)–(H4), with
`(zₙ)` bounded and `h` constant on the set `Ω` of cluster points and having the KL property at each
point of `Ω`, and `h̄ = h(z̄)` for `z̄ ∈ Ω₀`:
(i) `∑ Δₙ < +∞`;
(ii) under (H5), `∑ ‖xₙ₊₁ - xₙ‖ < +∞` and `(xₙ)` converges;
(iii) if `inf βₙ > 0`, then `0 ∈ ∂_L h(z̄)` for all `z̄ ∈ Ω₀`;
(iv) if moreover `h` has the KL property on `Ω` with an exponent `a ≤ 1/2`, `ı̲ ≤ 1`, `δ > 0` and
(21) holds, there are `γ₁ > 0` and `ρ ∈ (0, 1)` with `h(zₙ) - h̄ ≤ γ₁ρⁿ` for all `n`; and if in
addition (H5) holds and `∑_{k ≥ n} ε_k = O(√(h(z_{n-ı̄}) - h̄))`, there are `x̄` and `γ₂ > 0` with
`‖xₙ - x̄‖ ≤ γ₂ρ^{n/2}` for all `n` (the same `ρ`). -/
theorem native_theorem_5_2 {N : ℕ} {x : ℕ → EuclideanSpace ℝ (Fin N)} {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH2 : H2 h z β ε Δ ilo ihi lam) (hH3 : H3 h z) (hH4 : H4 α β ε)
    (hbdd : Bornology.IsBounded (Set.range z))
    (hconst : ∀ z₁ ∈ clusterSet z, ∀ z₂ ∈ clusterSet z, h z₁ = h z₂)
    (hKL : ∀ zbar ∈ clusterSet z, HasKLProperty h zbar) :
    Summable (fun n : ℕ => Δ n) ∧
    (H5 x Δ → Summable (fun n : ℕ => ‖x (n + 1) - x n‖) ∧
      ∃ xbar : EuclideanSpace ℝ (Fin N), Tendsto x atTop (𝓝 xbar)) ∧
    ((∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ β n) →
      ∀ zbar ∈ omega0 h z, (0 : EuclideanSpace ℝ (Fin P)) ∈ LimitingSubdiff h zbar) ∧
    (∀ a : ℝ, a ≤ 1 / 2 → (∀ zbar ∈ clusterSet z, HasKLPropertyExp h zbar a) →
      ilo ≤ 1 → ∀ d : ℝ, DeltaLowerBound α β ilo ihi d →
      (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        ε n / β n ≤ C * Real.sqrt ((h (z ((n : ℤ) - ihi).toNat)).toReal -
          (h (z ((n : ℤ) + 1 - ilo).toNat)).toReal)) →
      ∃ γ₁ : ℝ, 0 < γ₁ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        (∀ zbar ∈ omega0 h z, ∀ n : ℕ, (h (z n)).toReal - (h zbar).toReal ≤ γ₁ * ρ ^ n) ∧
        (H5 x Δ →
          (∃ zbar ∈ omega0 h z, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
            ∑' k : ℕ, ε (n + k) ≤
              C * Real.sqrt ((h (z ((n : ℤ) - ihi).toNat)).toReal - (h zbar).toReal)) →
          ∃ xbar : EuclideanSpace ℝ (Fin N), ∃ γ₂ : ℝ, 0 < γ₂ ∧
            ∀ n : ℕ, ‖x n - xbar‖ ≤ γ₂ * ρ ^ ((n : ℝ) / 2))) := by
  have hsum := native_finite_length hset hH1 hH2 hH3 hH4 hbdd hconst hKL
  refine ⟨hsum, fun hx => native_convergence hset hsum hx, ?_, ?_⟩
  · intro hb zbar hz
    exact native_stationarity hset hH1 hH2 hH4.2.2 hsum hb hz
  · intro a ha hexp hilo d hd herr
    obtain ⟨γ, hγ, ρ, hρ, hρ1, hval⟩ :=
      native_value_rate hset hH1 hH2 hH3 hbdd hconst ha hexp hilo hd herr
    refine ⟨γ, hγ, ρ, hρ, hρ1, hval, ?_⟩
    intro hx _herrtail
    obtain ⟨l, _, he, hcl, hlo⟩ := uniform_value_limit hset hH1 hH2 hH3 hconst
    obtain ⟨zt, hzt⟩ := cluster_nonempty hbdd
    have hz : zt ∈ omega0 h z := by
      refine ⟨hzt, ?_⟩
      simpa only [hcl zt hzt] using he
    have hv : ∀ n, (h (z n)).toReal-l ≤ γ * ρ ^ n := by
      intro n
      simpa only [hcl zt hzt, EReal.toReal_coe] using hval zt hz n
    exact native_iterate_rate hset hH1 hH2 hH4.1 l γ ρ hlo hγ hρ hρ1 hv hx

end FracPSG.Abstract.Fresh
end

open FracPSG.Abstract NonconvexSplitting.Shared NonconvexSplitting.ADMMKL

theorem solution {N : ℕ} {x : ℕ → EuclideanSpace ℝ (Fin N)} {P : ℕ} {h : EuclideanSpace ℝ (Fin P) → EReal}
    {z : ℕ → EuclideanSpace ℝ (Fin P)} {α β ε : ℕ → ℝ} {Δ : ℤ → ℝ} {ilo ihi : ℤ}
    {lam : ℤ → ℝ}
    (hset : AbstractSetting h α β ε Δ ilo ihi lam)
    (hH1 : H1 h z α Δ) (hH2 : H2 h z β ε Δ ilo ihi lam) (hH3 : H3 h z) (hH4 : H4 α β ε)
    (hbdd : Bornology.IsBounded (Set.range z))
    (hconst : ∀ z₁ ∈ clusterSet z, ∀ z₂ ∈ clusterSet z, h z₁ = h z₂)
    (hKL : ∀ zbar ∈ clusterSet z, HasKLProperty h zbar) :
    Summable (fun n : ℕ => Δ n) ∧
    (H5 x Δ → Summable (fun n : ℕ => ‖x (n + 1) - x n‖) ∧
      ∃ xbar : EuclideanSpace ℝ (Fin N), Tendsto x atTop (𝓝 xbar)) ∧
    ((∃ b : ℝ, 0 < b ∧ ∀ n, b ≤ β n) →
      ∀ zbar ∈ omega0 h z, (0 : EuclideanSpace ℝ (Fin P)) ∈ LimitingSubdiff h zbar) ∧
    (∀ a : ℝ, a ≤ 1 / 2 → (∀ zbar ∈ clusterSet z, HasKLPropertyExp h zbar a) →
      ilo ≤ 1 → ∀ d : ℝ, DeltaLowerBound α β ilo ihi d →
      (∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        ε n / β n ≤ C * Real.sqrt ((h (z ((n : ℤ) - ihi).toNat)).toReal -
          (h (z ((n : ℤ) + 1 - ilo).toNat)).toReal)) →
      ∃ γ₁ : ℝ, 0 < γ₁ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
        (∀ zbar ∈ omega0 h z, ∀ n : ℕ, (h (z n)).toReal - (h zbar).toReal ≤ γ₁ * ρ ^ n) ∧
        (H5 x Δ →
          (∃ zbar ∈ omega0 h z, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
            ∑' k : ℕ, ε (n + k) ≤
              C * Real.sqrt ((h (z ((n : ℤ) - ihi).toNat)).toReal - (h zbar).toReal)) →
          ∃ xbar : EuclideanSpace ℝ (Fin N), ∃ γ₂ : ℝ, 0 < γ₂ ∧
            ∀ n : ℕ, ‖x n - xbar‖ ≤ γ₂ * ρ ^ ((n : ℝ) / 2))) := by
  exact Fresh.native_theorem_5_2 (x := x) hset hH1 hH2 hH3 hH4 hbdd hconst hKL
