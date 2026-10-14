-- Prove2me | solution 1 for DistCov.Hilbert.hilbert_strict_negType
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T21:05:06.402146+00:00
-- url     : https://prove2.me/submissions/3148ae55-9084-4edf-b4bf-7f86c8b33348

import Theorems.Thm_DistCov_Hilbert_gaussEmb_isometry
import Theorems.Thm_DistCov_Hilbert_gaussian_series

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace MeasureTheory.Measure
open scoped Topology NNReal
namespace DistCovStrict
open DistCov.Hilbert
abbrev E := DistCov.Indep.L2N
abbrev Ω := ℕ → ℝ
abbrev P := Ω × ℝ
local instance : IsProbabilityMeasure rho := by unfold rho; infer_instance

lemma quadratic_identity {ι : Type*} [Fintype ι] (α a : ι → ℝ) (h : ∑ i, α i = 0) :
    (∑ i, ∑ j, α i * α j * (a i - a j)^2) = -2 * (∑ i, α i * a i)^2 := by
  classical
  have he (i j : ι) : α i * α j * (a i - a j)^2 =
      (α i * (a i)^2) * α j + α i * (α j * (a j)^2) - 2 * (α i * a i) * (α j * a j) := by ring
  simp_rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, h, mul_zero, zero_mul, zero_add, zero_sub]
  rw [← Finset.mul_sum]
  ring

def Q {n : ℕ} (x : Fin n → E) (α : Fin n → ℝ) (p : P) : ℝ :=
  ∑ i, ∑ j, α i * α j * (gaussEmb (x i) p - gaussEmb (x j) p)^2

lemma Q_integrable {n : ℕ} (x : Fin n → E) (α : Fin n → ℝ) :
    Integrable (Q x α) (rho.prod volume) := by
  unfold Q
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (gaussEmb_isometry (x i) (x j)).1.const_mul _

lemma Q_integral {n : ℕ} (x : Fin n → E) (α : Fin n → ℝ) :
    (∫ p, Q x α p ∂(rho.prod volume)) = ∑ i, ∑ j, α i * α j * dist (x i) (x j) := by
  unfold Q
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul, (gaussEmb_isometry (x i) (x j)).2.1, dist_eq_norm]
    · intro j hj
      exact (gaussEmb_isometry (x i) (x j)).1.const_mul _
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (gaussEmb_isometry (x i) (x j)).1.const_mul _

lemma negType_l2 : DistCov.Indep.NegType E := by
  intro n x α hα
  rw [← Q_integral x α]
  apply integral_nonpos
  intro p
  change Q x α p ≤ 0
  unfold Q
  rw [quadratic_identity α (fun i => gaussEmb (x i) p) hα]
  nlinarith [sq_nonneg (∑ i, α i * gaussEmb (x i) p)]

lemma c_pos : 0 < cGauss := by
  have hi : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num)).abs
  let : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  unfold cGauss
  apply (integral_pos_iff_support_of_nonneg (fun z => abs_nonneg z) hi).mpr
  have he : Function.support (fun z : ℝ => |z|) = ({0} : Set ℝ)ᶜ := by
    ext z; simp [Function.support]
  rw [he, measure_compl (measurableSet_singleton 0) (by simp)]
  simp

lemma eval_sub (u v : E) : (fun w => wEval w u - wEval w v) =ᵐ[rho]
    (fun w => wEval w (u-v : E)) := by
  filter_upwards [(gaussian_series u).1, (gaussian_series v).1,
    (gaussian_series (u-v)).1] with w hu hv hd
  have hd' : Tendsto (fun N => (∑ n ∈ Finset.range N, u n * w n) -
      ∑ n ∈ Finset.range N, v n * w n) atTop (𝓝 (wEval w (u-v : E))) := by
    simpa only [lp.coeFn_sub, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib] using hd
  exact tendsto_nhds_unique (hu.sub hv) hd'

lemma eval_meas (u : E) : Measurable (fun w : Ω => wEval w u) := by
  unfold wEval
  exact Measurable.limsup (fun N => by fun_prop)

lemma eval_ne_ae (u v : E) (h : u ≠ v) : ∀ᵐ w ∂rho, wEval w u ≠ wEval w v := by
  have hn : ‖u-v‖₊ ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using sub_ne_zero.mpr h)
  let : NullSingletonClass (gaussianReal 0 (‖u-v‖₊ ^ 2)) := nullSingletonClass_gaussianReal hn
  have hz : ∀ᵐ w ∂rho, wEval w (u-v : E) ≠ 0 := by
    have hm := (gaussian_series (u-v)).2.1
    have he := congrArg (fun M : Measure ℝ => M ({0} : Set ℝ)) hm
    rw [Measure.map_apply (eval_meas _) (measurableSet_singleton 0)] at he
    apply ae_iff.mpr
    simpa only [Set.preimage, Set.mem_singleton_iff, measure_singleton, lp.coeFn_sub, Pi.sub_apply, not_not] using he
  filter_upwards [hz, eval_sub u v] with w hw he
  intro heq
  exact hw (by rw [← he,heq,sub_self])


lemma rays_independent {n : ℕ} (a α : Fin n → ℝ) (ha : Function.Injective a)
    (h : ∀ᵐ s ∂volume, ∑ i, α i * (Ici (a i)).indicator (fun _ => (1 : ℝ)) s = 0) : α = 0 := by
  classical
  have hd : Dense {s : ℝ | ∑ i, α i * (Ici (a i)).indicator (fun _ => (1 : ℝ)) s = 0} := dense_of_ae h
  funext i
  obtain ⟨l, _, hl, hlim⟩ := hd.exists_seq_strictMono_tendsto (a i)
  obtain ⟨r, _, hr, hrim⟩ := hd.exists_seq_strictAnti_tendsto (a i)
  have he : ∀ᶠ s in 𝓝 (a i), ∀ j : Fin n, j ≠ i → (a j ≤ s ↔ a j ≤ a i) := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = i
    · exact Eventually.of_forall fun s hji => (hji hj).elim
    · have hne : a j ≠ a i := fun he => hj (ha he)
      rcases lt_or_gt_of_ne hne with hjl | hjr
      · exact (eventually_gt_nhds hjl).mono fun s hs _ => ⟨fun _ => hjl.le, fun _ => hs.le⟩
      · exact (eventually_lt_nhds hjr).mono fun s hs _ => ⟨fun hh => (not_lt_of_ge hh hs).elim, fun hh => (not_lt_of_ge hh hjr).elim⟩
  obtain ⟨N,hNl,hNr⟩ := ((hlim.eventually he).and (hrim.eventually he)).exists
  have hi : α i = ∑ j, (α j * (Ici (a j)).indicator (fun _ => (1 : ℝ)) (r N) -
      α j * (Ici (a j)).indicator (fun _ => (1 : ℝ)) (l N)) := by
    symm
    rw [Finset.sum_eq_single i]
    · simp [show a i ≤ r N from (hr N).1.le, show ¬ a i ≤ l N from not_le.mpr (hl N).1]
    · intro j hj hji
      have hh : a j ≤ r N ↔ a j ≤ l N := (hNr j hji).trans (hNl j hji).symm
      by_cases hleft : a j ≤ l N
      · simp [Set.indicator_of_mem, show r N ∈ Ici (a j) from hh.mpr hleft, hleft]
      · simp [Set.indicator_of_notMem, hleft, show ¬ a j ≤ r N from fun hh' => hleft (hh.mp hh')]
    · simp
  change α i = 0
  rw [hi, Finset.sum_sub_distrib, (hr N).2, (hl N).2, sub_self]

lemma Q_zero_rays {n : ℕ} (x : Fin n → E) (α : Fin n → ℝ) (hα : ∑ i, α i = 0)
    (hQ : ∑ i, ∑ j, α i * α j * dist (x i) (x j) = 0) :
    ∀ᵐ p ∂(rho.prod volume), ∑ i, α i * (Ici (wEval p.1 (x i) / cGauss)).indicator (fun _ => (1 : ℝ)) p.2 = 0 := by
  have hn : ∀ p, 0 ≤ -Q x α p := by
    intro p
    unfold Q
    rw [quadratic_identity α (fun i => gaussEmb (x i) p) hα]
    nlinarith [sq_nonneg (∑ i, α i * gaussEmb (x i) p)]
  have hI : ∫ p, -Q x α p ∂(rho.prod volume) = 0 := by
    rw [integral_neg, Q_integral, hQ, neg_zero]
  have he := (integral_eq_zero_iff_of_nonneg hn (Q_integrable x α).neg).mp hI
  filter_upwards [he] with p hp
  change -Q x α p = 0 at hp
  unfold Q at hp
  rw [quadratic_identity α (fun i => gaussEmb (x i) p) hα] at hp
  have hf : ∑ i, α i * gaussEmb (x i) p = 0 := by nlinarith [sq_nonneg (∑ i, α i * gaussEmb (x i) p)]
  unfold gaussEmb at hf
  simp_rw [mul_sub] at hf
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hα, zero_mul, sub_zero] at hf
  exact hf

lemma strict_l2 {n : ℕ} (x : Fin n → E) (α : Fin n → ℝ) (hx : Function.Injective x)
    (hα : ∑ i, α i = 0) (hQ : ∑ i, ∑ j, α i * α j * dist (x i) (x j) = 0) : α = 0 := by
  have he := ae_ae_of_ae_prod (Q_zero_rays x α hα hQ)
  have hd : ∀ᵐ w ∂rho, ∀ i j : Fin n, i ≠ j → wEval w (x i) ≠ wEval w (x j) := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall fun w hn => (hn hij).elim
    · exact (eval_ne_ae (x i) (x j) (fun he => hij (hx he))).mono fun w hw _ => hw
  obtain ⟨w,hw,hwd⟩ := (he.and hd).exists
  apply rays_independent (fun i => wEval w (x i) / cGauss) α _ hw
  intro i j hij
  by_contra hne
  exact hwd i j hne ((div_left_inj' c_pos.ne').mp hij)

def basisMap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {k : ℕ} (b : OrthonormalBasis (Fin k) ℝ H) : H →ₗ[ℝ] E where
  toFun u := ∑ i : Fin k, lp.single 2 i.val (b.repr u i)
  map_add' u v := by
    simp only [map_add, PiLp.add_apply, lp.single_add, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [map_smul, PiLp.smul_apply, lp.single_smul, Finset.smul_sum, RingHom.id_apply]

lemma basisMap_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {k : ℕ} (b : OrthonormalBasis (Fin k) ℝ H) (u v : H) :
    inner ℝ (basisMap b u) (basisMap b v) = inner ℝ u v := by
  classical
  change inner ℝ (∑ i : Fin k, (lp.single 2 i.val (b.repr u i) : E))
    (∑ j : Fin k, (lp.single 2 j.val (b.repr v j) : E)) = _
  rw [sum_inner]
  simp_rw [inner_sum, lp.inner_single_left, lp.coeFn_single]
  have hi (i : Fin k) : (∑ j : Fin k, inner ℝ (b.repr u i)
      ((Pi.single j.val (b.repr v j) : ℕ → ℝ) i.val)) = inner ℝ (b.repr u i) (b.repr v i) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have hne : i.val ≠ j.val := fun he => hji (Fin.ext he.symm)
      simp [Pi.single_eq_of_ne hne]
    · simp
  simp_rw [hi]
  rw [← PiLp.inner_apply, b.repr.inner_map_map]

lemma finite_isometric_copy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (x : Fin n → H) : ∃ y : Fin n → E, ∀ i j, dist (y i) (y j) = dist (x i) (x j) := by
  classical
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range x)
  letI : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range x)
  let b := stdOrthonormalBasis ℝ S
  let f : S →ₗᵢ[ℝ] E := (basisMap b).isometryOfInner (basisMap_inner b)
  let z : Fin n → S := fun i => ⟨x i, Submodule.subset_span ⟨i,rfl⟩⟩
  refine ⟨fun i => f (z i), ?_⟩
  intro i j
  rw [f.dist_map]
  rfl
end DistCovStrict

open DistCov.Hilbert

theorem solution (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] :
    DistCov.Indep.NegType H ∧
    ∀ (n : ℕ) (x : Fin n → H) (α : Fin n → ℝ), Function.Injective x → ∑ i, α i = 0 →
      ∑ i, ∑ j, α i * α j * dist (x i) (x j) = 0 → α = 0 := by
  constructor
  · intro n x α hα
    obtain ⟨y,hy⟩ := DistCovStrict.finite_isometric_copy x
    simpa only [hy] using DistCovStrict.negType_l2 n y α hα
  · intro n x α hx hα hQ
    obtain ⟨y,hy⟩ := DistCovStrict.finite_isometric_copy x
    have hiy : Function.Injective y := by
      intro i j hij
      apply hx
      apply dist_eq_zero.mp
      rw [← hy, hij, dist_self]
    apply DistCovStrict.strict_l2 y α hiy hα
    simpa only [hy] using hQ
#print axioms solution
