-- Prove2me | solution 1 for BilinearGramian.Kernel.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-21T07:33:21.547545+00:00
-- url     : https://prove2.me/submissions/9d68b1af-8c94-4fee-ab8c-b5c731337204

import Mathlib
import Definitions.Def_BilinearGramian_Kernel_System
import Definitions.Def_BilinearGramian_Kernel_GramianEquations

open Matrix
open scoped BigOperators Classical
open Matrix BilinearGramian.Kernel

namespace BilinearGramianProof
end BilinearGramianProof

open scoped BigOperators Classical
open Matrix BilinearGramian.Kernel

namespace BilinearGramianProof

theorem dot_transpose {n p : ℕ} (C : Matrix (Fin p) (Fin n) ℝ)
    (v : Fin n → ℝ) (w : Fin p → ℝ) :
    v ⬝ᵥ (Cᵀ *ᵥ w) = (C *ᵥ v) ⬝ᵥ w := by
  rw [dotProduct_transpose_mulVec, dotProduct_comm]

theorem psd_quad_nonneg {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosSemidef) (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ (Q *ᵥ v) := by
  simpa using hQ.dotProduct_mulVec_nonneg v

theorem obs_kernel {n m p : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {N : Fin m → Matrix (Fin n) (Fin n) ℝ}
    {C : Matrix (Fin p) (Fin n) ℝ} {Q : Matrix (Fin n) (Fin n) ℝ}
    (hQ : Q.PosSemidef) (heq : ObsGramianEq A N C Q)
    {v : Fin n → ℝ} (hv : Q *ᵥ v = 0) :
    Q *ᵥ (A *ᵥ v) = 0 ∧ (∀ j, Q *ᵥ (N j *ᵥ v) = 0) ∧ C *ᵥ v = 0 := by
  have hsym : Qᵀ = Q := by simpa using hQ.isHermitian.eq
  have hleft (w : Fin n → ℝ) : v ⬝ᵥ (Q *ᵥ w) = 0 := by
    rw [← hsym, dot_transpose, hv, zero_dotProduct]
  have hquad := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => v ⬝ᵥ (M *ᵥ v)) heq
  change v ⬝ᵥ ((Aᵀ * Q + Q * A + ∑ j, (N j)ᵀ * Q * N j) *ᵥ v) =
    v ⬝ᵥ ((-(Cᵀ * C)) *ᵥ v) at hquad
  simp only [add_mulVec, sum_mulVec, ← mulVec_mulVec, dotProduct_add, dotProduct_sum,
    neg_mulVec, dotProduct_neg, hv, mulVec_zero, hleft,
    zero_add, dot_transpose] at hquad
  have hn (j : Fin m) : 0 ≤ (N j *ᵥ v) ⬝ᵥ (Q *ᵥ (N j *ᵥ v)) :=
    psd_quad_nonneg hQ _
  have hc0 : 0 ≤ (C *ᵥ v) ⬝ᵥ (C *ᵥ v) := by
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hs0 : 0 ≤ ∑ j, (N j *ᵥ v) ⬝ᵥ (Q *ᵥ (N j *ᵥ v)) :=
    Finset.sum_nonneg fun j _ => hn j
  have hc : C *ᵥ v = 0 := dotProduct_self_eq_zero.mp (by linarith)
  have hs : ∑ j, (N j *ᵥ v) ⬝ᵥ (Q *ᵥ (N j *ᵥ v)) = 0 := by linarith
  have hN (j : Fin m) : Q *ᵥ (N j *ᵥ v) = 0 := by
    have hj : (N j *ᵥ v) ⬝ᵥ (Q *ᵥ (N j *ᵥ v)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp hs j (Finset.mem_univ j)
    exact (hQ.dotProduct_mulVec_zero_iff _).mp (by simpa using hj)
  have happ := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M *ᵥ v) heq
  change (Aᵀ * Q + Q * A + ∑ j, (N j)ᵀ * Q * N j) *ᵥ v =
    (-(Cᵀ * C)) *ᵥ v at happ
  simp only [add_mulVec, sum_mulVec, ← mulVec_mulVec, neg_mulVec, hv, hc, hN,
    mulVec_zero, Finset.sum_const_zero, zero_add, add_zero, neg_zero] at happ
  exact ⟨happ, hN, hc⟩

theorem reach_kernel {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {N : Fin m → Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) (heq : ReachGramianEq A N B P)
    {v : Fin n → ℝ} (hv : P *ᵥ v = 0) :
    P *ᵥ (Aᵀ *ᵥ v) = 0 ∧ (∀ j, P *ᵥ ((N j)ᵀ *ᵥ v) = 0) ∧ Bᵀ *ᵥ v = 0 := by
  apply obs_kernel hP (A := Aᵀ) (N := fun j => (N j)ᵀ) (C := Bᵀ) _ hv
  simpa [ObsGramianEq, ReachGramianEq] using heq

end BilinearGramianProof

open scoped BigOperators Classical
open Matrix BilinearGramian.Kernel

namespace BilinearGramianProof

theorem mem_range_iff_kernel_dot {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) (x : Fin n → ℝ) :
    x ∈ LinearMap.range (Matrix.toLin' P) ↔ ∀ v, P *ᵥ v = 0 → v ⬝ᵥ x = 0 := by
  let L := Matrix.toEuclideanLin P
  have hsym : L.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP.isHermitian
  have horth : (LinearMap.ker L)ᗮ = LinearMap.range L := by
    rw [← hsym.orthogonal_range, Submodule.orthogonal_orthogonal]
  have hr : x ∈ LinearMap.range (Matrix.toLin' P) ↔
      (WithLp.toLp 2 x) ∈ LinearMap.range L := by
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨WithLp.toLp 2 y, congrArg (WithLp.toLp 2) hy⟩
    · rintro ⟨y, hy⟩
      exact ⟨WithLp.ofLp y, congrArg WithLp.ofLp hy⟩
  rw [hr, ← horth, Submodule.mem_orthogonal]
  constructor
  · intro h v hv
    have hm : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ∈ LinearMap.ker L := by
      change WithLp.toLp 2 (P *ᵥ v) = 0
      simp [hv]
    simpa [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using h (WithLp.toLp 2 v) hm
  · intro h v hv
    have hm : P *ᵥ WithLp.ofLp v = 0 := congrArg WithLp.ofLp hv
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using h (WithLp.ofLp v) hm

theorem reach_range {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {N : Fin m → Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) (heq : ReachGramianEq A N B P) :
    (∀ v ∈ LinearMap.range (Matrix.toLin' P),
      A *ᵥ v ∈ LinearMap.range (Matrix.toLin' P)) ∧
    (∀ j, ∀ v ∈ LinearMap.range (Matrix.toLin' P),
      N j *ᵥ v ∈ LinearMap.range (Matrix.toLin' P)) ∧
    (∀ w, B *ᵥ w ∈ LinearMap.range (Matrix.toLin' P)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    apply (mem_range_iff_kernel_dot hP _).mpr
    intro z hz
    have ht := (mem_range_iff_kernel_dot hP v).mp hv (Aᵀ *ᵥ z) (reach_kernel hP heq hz).1
    simpa only [← dot_transpose Aᵀ, transpose_transpose] using ht
  · intro j v hv
    apply (mem_range_iff_kernel_dot hP _).mpr
    intro z hz
    have ht := (mem_range_iff_kernel_dot hP v).mp hv ((N j)ᵀ *ᵥ z)
      ((reach_kernel hP heq hz).2.1 j)
    simpa only [← dot_transpose (N j)ᵀ, transpose_transpose] using ht
  · intro w
    apply (mem_range_iff_kernel_dot hP _).mpr
    intro z hz
    rw [← transpose_transpose B, dot_transpose Bᵀ, (reach_kernel hP heq hz).2.2,
      zero_dotProduct]

end BilinearGramianProof

open Set Filter MeasureTheory
open scoped Topology

namespace BilinearGramianProof

/-- Zero uniqueness for an integral equation with a nonnegative integrable coefficient. -/
theorem integral_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} (hT : 0 ≤ T) (z g : ℝ → E) (k : ℝ → ℝ)
    (hz : ContinuousOn z (Icc 0 T))
    (hg : IntervalIntegrable g volume 0 T)
    (hk : IntervalIntegrable k volume 0 T)
    (hk0 : ∀ s ∈ Icc 0 T, 0 ≤ k s)
    (hint : ∀ t ∈ Icc 0 T, z t = ∫ s in (0 : ℝ)..t, g s)
    (hbound : ∀ s ∈ Icc 0 T, ‖g s‖ ≤ k s * ‖z s‖) :
    ∀ t ∈ Icc 0 T, z t = 0 := by
  have hgsub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
      IntervalIntegrable g volume a b :=
    hg.mono_set (by simpa only [uIcc_of_le hab, uIcc_of_le hT] using
      Icc_subset_Icc ha hb)
  have hksub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
      IntervalIntegrable k volume a b :=
    hk.mono_set (by simpa only [uIcc_of_le hab, uIcc_of_le hT] using
      Icc_subset_Icc ha hb)
  let Z : Set ℝ := {t | z t = 0}
  have hclosed : IsClosed (Z ∩ Icc 0 T) := by
    have h := isClosed_Icc.isClosed_eq hz
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : E)) _)
    convert h using 1
    ext t
    simp only [Z, mem_inter_iff, mem_ofPred_eq, and_comm]
  have hz0 : (0 : ℝ) ∈ Z := by
    change z 0 = 0
    simpa using hint 0 ⟨le_rfl, hT⟩
  have hall : Icc 0 T ⊆ Z := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsWithin hz0
    rintro a ⟨hza, ha0, haT⟩
    change z a = 0 at hza
    have hprim : ContinuousWithinAt (fun b => ∫ s in a..b, k s) (Icc 0 T) a := by
      have hp := intervalIntegral.continuousOn_primitive_interval' hk
        (show a ∈ uIcc 0 T by rw [uIcc_of_le hT]; exact ⟨ha0, haT.le⟩)
      rw [uIcc_of_le hT] at hp
      exact hp a ⟨ha0, haT.le⟩
    obtain ⟨δ, hδ, hsmall⟩ := Metric.continuousWithinAt_iff.mp hprim (1 / 2) (by norm_num)
    obtain ⟨b, hab, hb⟩ := exists_between (lt_min haT (lt_add_of_pos_right a hδ))
    have hbT : b ≤ T := (hb.trans_le (min_le_left _ _)).le
    have hbδ : b - a < δ := by have := hb.trans_le (min_le_right _ _); linarith
    have hsmallb : (∫ s in a..b, k s) < 1 / 2 := by
      have h := hsmall ⟨ha0.trans hab.le, hbT⟩
        (show dist b a < δ by simpa only [Real.dist_eq, abs_of_pos (sub_pos.mpr hab)] using hbδ)
      simp only [intervalIntegral.integral_same, Real.dist_eq, sub_zero] at h
      exact (le_abs_self _).trans_lt h
    obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab.le⟩
      (hz.norm.mono (Icc_subset_Icc ha0 hbT))
    have hcT : c ∈ Icc 0 T := ⟨ha0.trans hc.1, hc.2.trans hbT⟩
    have hzc : z c = ∫ s in a..c, g s := by
      have h := intervalIntegral.integral_add_adjacent_intervals
        (hgsub (a := 0) le_rfl ha0 haT.le) (hgsub ha0 hc.1 hcT.2)
      rw [← hint a ⟨ha0, haT.le⟩, ← hint c hcT, hza, zero_add] at h
      exact h.symm
    have hnorm : ‖z c‖ ≤ ‖z c‖ * (∫ s in a..c, k s) := by
      calc
        ‖z c‖ = ‖∫ s in a..c, g s‖ := congrArg norm hzc
        _ ≤ ∫ s in a..c, ‖z c‖ * k s := ?_
        _ = ‖z c‖ * (∫ s in a..c, k s) := intervalIntegral.integral_const_mul _ _
      apply intervalIntegral.norm_integral_le_of_norm_le hc.1
      · exact Filter.Eventually.of_forall fun s hs => by
          have hsT : s ∈ Icc 0 T := ⟨ha0.trans hs.1.le, hs.2.trans hcT.2⟩
          calc
            ‖g s‖ ≤ k s * ‖z s‖ := hbound s hsT
            _ ≤ k s * ‖z c‖ := mul_le_mul_of_nonneg_left
              (hmax ⟨hs.1.le, hs.2.trans hc.2⟩) (hk0 s hsT)
            _ = ‖z c‖ * k s := mul_comm _ _
      · exact (hksub ha0 hc.1 hcT.2).const_mul _
    have hmono : (∫ s in a..c, k s) ≤ ∫ s in a..b, k s := by
      apply intervalIntegral.integral_mono_interval le_rfl hc.1 hc.2
      · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun s hs =>
          hk0 s ⟨ha0.trans hs.1.le, hs.2.trans hbT⟩)
      · exact hksub ha0 hab.le hbT
    have hM : ‖z c‖ = 0 := by
      have h := hnorm.trans (mul_le_mul_of_nonneg_left hmono (norm_nonneg _))
      nlinarith [norm_nonneg (z c)]
    have hzab : ∀ s ∈ Icc a b, z s = 0 := by
      intro s hs
      apply norm_eq_zero.mp
      exact le_antisymm (hM ▸ hmax hs) (norm_nonneg _)
    apply Filter.mem_of_superset (Ioc_mem_nhdsGT hab)
    intro s hs
    exact hzab s ⟨hs.1.le, hs.2⟩
  exact fun t ht => hall ht

end BilinearGramianProof

open Matrix BilinearGramian.Kernel Set MeasureTheory
open scoped BigOperators Classical

namespace BilinearGramianProof

/-- A finite-dimensional invariant submodule contains every actual integral-equation solution. -/
theorem solution_mem_submodule {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ)
    (S : Submodule ℝ (Fin n → ℝ))
    (hA : ∀ z ∈ S, A *ᵥ z ∈ S)
    (hN : ∀ j z, z ∈ S → N j *ᵥ z ∈ S)
    (hB : ∀ w, B *ᵥ w ∈ S)
    (u : ℝ → Fin m → ℝ) (x0 : Fin n → ℝ) (x : ℝ → Fin n → ℝ)
    (hx0 : x0 ∈ S) (hu : IsInput u)
    (hx : IsSolution A N B u x0 x) :
    ∀ t : ℝ, 0 ≤ t → x t ∈ S := by
  have : IsClosed (S : Set (Fin n → ℝ)) := S.closed_of_finiteDimensional
  let q : (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) ⧸ S) := S.mkQL
  let A₀ : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := (Matrix.toLin' A).toContinuousLinearMap
  let N₀ : Fin m → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    fun j => (Matrix.toLin' (N j)).toContinuousLinearMap
  have hq {v : Fin n → ℝ} (hv : v ∈ S) : q v = 0 :=
    (Submodule.Quotient.mk_eq_zero S).mpr hv
  have hqA : S ≤ (q.comp A₀).ker := by
    intro v hv
    change q (A *ᵥ v) = 0
    exact hq (hA v hv)
  have hqN (j : Fin m) : S ≤ (q.comp (N₀ j)).ker := by
    intro v hv
    change q (N j *ᵥ v) = 0
    exact hq (hN j v hv)
  let Aq := S.liftQL (q.comp A₀) hqA
  let Nq := fun j => S.liftQL (q.comp (N₀ j)) (hqN j)
  have hAq (v : Fin n → ℝ) : Aq (q v) = q (A *ᵥ v) := rfl
  have hNq (j : Fin m) (v : Fin n → ℝ) : Nq j (q v) = q (N j *ᵥ v) := rfl
  have hfield (v : Fin n → ℝ) (w : Fin m → ℝ) :
      q (field A N B v w) = Aq (q v) + ∑ j, w j • Nq j (q v) := by
    simp only [field, map_add, map_sum, map_smul, hAq, hNq, hq (hB w), add_zero]
  have hnorm (v : Fin n → ℝ) (w : Fin m → ℝ) :
      ‖q (field A N B v w)‖ ≤ (‖Aq‖ + ∑ j, |w j| * ‖Nq j‖) * ‖q v‖ := by
    rw [hfield]
    calc
      ‖Aq (q v) + ∑ j, w j • Nq j (q v)‖ ≤
          ‖Aq (q v)‖ + ∑ j, ‖w j • Nq j (q v)‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ ‖Aq‖ * ‖q v‖ + ∑ j, |w j| * (‖Nq j‖ * ‖q v‖) := by
        apply add_le_add (Aq.le_opNorm _)
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ((Nq j).le_opNorm _) (abs_nonneg _)
      _ = (‖Aq‖ + ∑ j, |w j| * ‖Nq j‖) * ‖q v‖ := by
        rw [add_mul, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
  intro T hT
  let z : ℝ → ((Fin n → ℝ) ⧸ S) := fun t => q (x t)
  let g : ℝ → ((Fin n → ℝ) ⧸ S) := fun t => q (field A N B (x t) (u t))
  let k : ℝ → ℝ := fun t => ‖Aq‖ + ∑ j, |u t j| * ‖Nq j‖
  have hz : ContinuousOn z (Icc 0 T) :=
    q.continuous.comp_continuousOn (hx.1.mono Icc_subset_Ici_self)
  have hg : IntervalIntegrable g volume 0 T :=
    ⟨q.integrable_comp (hx.2 T hT).1.1, q.integrable_comp (hx.2 T hT).1.2⟩
  have hui (j : Fin m) : IntervalIntegrable (fun t => |u t j|) volume 0 T := by
    have hi := (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ).integrable_comp (hu T)
    have hi' : IntegrableOn (fun t => |u t j|) (Icc 0 T) := by
      simpa only [IntegrableOn, ContinuousLinearMap.proj_apply, Real.norm_eq_abs] using hi.norm
    apply MeasureTheory.IntegrableOn.intervalIntegrable
    simpa only [uIcc_of_le hT] using hi'
  have hk : IntervalIntegrable k volume 0 T := by
    apply intervalIntegrable_const.add
    convert! (IntervalIntegrable.sum Finset.univ fun j _ => (hui j).mul_const ‖Nq j‖) using 1
    ext t
    simp only [Finset.sum_apply]
  have hk0 : ∀ s ∈ Icc 0 T, 0 ≤ k s := by
    intro s _
    exact add_nonneg Aq.opNorm_nonneg (Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (Nq j).opNorm_nonneg)
  have hint : ∀ t ∈ Icc 0 T, z t = ∫ s in (0 : ℝ)..t, g s := by
    intro t ht
    change q (x t) = ∫ s in (0 : ℝ)..t, q (field A N B (x s) (u s))
    rw [q.intervalIntegral_comp_comm (hx.2 t ht.1).1, (hx.2 t ht.1).2,
      map_add, hq hx0, zero_add]
  have hzero := integral_zero hT z g k hz hg hk hk0 hint (fun s _ => hnorm (x s) (u s))
  exact (Submodule.Quotient.mk_eq_zero S).mp (hzero T ⟨hT, le_rfl⟩)

/-- The homogeneous native equation is the zero-forcing instance, with the same input class. -/
theorem hom_solution_mem_submodule {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (S : Submodule ℝ (Fin n → ℝ))
    (hA : ∀ z ∈ S, A *ᵥ z ∈ S)
    (hN : ∀ j z, z ∈ S → N j *ᵥ z ∈ S)
    (u : ℝ → Fin m → ℝ) (x0 : Fin n → ℝ) (x : ℝ → Fin n → ℝ)
    (hx0 : x0 ∈ S) (hu : IsInput u)
    (hx : IsHomSolution A N u x0 x) :
    ∀ t : ℝ, 0 ≤ t → x t ∈ S := by
  apply solution_mem_submodule A N (0 : Matrix (Fin n) (Fin m) ℝ) S hA hN
    (fun w => by simp) u x0 x hx0 hu
  simpa only [IsSolution, IsHomSolution, field, homField, zero_mulVec, add_zero] using hx

end BilinearGramianProof

open Matrix BilinearGramianProof

namespace BilinearGramian.Kernel

/-- Benner–Damm 2011, Theorem 3.1, p. 695.
(a) If `P ≥ 0` solves the first equation of (3.6), every solution of the bilinear system (3.1)
started at `x(0) = 0` stays in `Im P` for all `t ≥ 0`, for every admissible input `u`.
(b) If `Q ≥ 0` solves the second equation of (3.6) and `x0 ∈ Ker Q`, every solution of the
homogeneous bilinear system (3.5) started at `x0` has output `y(t) = C x(t) = 0` for all `t ≥ 0`,
for every admissible input `u` (in particular for `u = 0`). -/
theorem theorem_3_1 {n m p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) :
    (∀ P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → ReachGramianEq A N B P →
      ∀ (u : ℝ → Fin m → ℝ) (x : ℝ → Fin n → ℝ), IsInput u → IsSolution A N B u 0 x →
        ∀ t : ℝ, 0 ≤ t → x t ∈ LinearMap.range (Matrix.toLin' P)) ∧
    (∀ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosSemidef → ObsGramianEq A N C Q →
      ∀ x0 : Fin n → ℝ, x0 ∈ LinearMap.ker (Matrix.toLin' Q) →
        ∀ (u : ℝ → Fin m → ℝ) (x : ℝ → Fin n → ℝ), IsInput u → IsHomSolution A N u x0 x →
          ∀ t : ℝ, 0 ≤ t → C *ᵥ x t = 0) := by
  constructor
  · intro P hP heq u x hu hx t ht
    obtain ⟨hA, hN, hB⟩ := reach_range hP heq
    exact solution_mem_submodule A N B (LinearMap.range (Matrix.toLin' P))
      hA hN hB u 0 x (Submodule.zero_mem _) hu hx t ht
  · intro Q hQ heq x0 hx0 u x hu hx t ht
    have hA : ∀ z ∈ LinearMap.ker (Matrix.toLin' Q),
        A *ᵥ z ∈ LinearMap.ker (Matrix.toLin' Q) := by
      intro z hz
      exact (obs_kernel hQ heq hz).1
    have hN : ∀ j z, z ∈ LinearMap.ker (Matrix.toLin' Q) →
        N j *ᵥ z ∈ LinearMap.ker (Matrix.toLin' Q) := by
      intro j z hz
      exact (obs_kernel hQ heq hz).2.1 j
    have hz := hom_solution_mem_submodule A N (LinearMap.ker (Matrix.toLin' Q))
      hA hN u x0 x hx0 hu hx t ht
    exact (obs_kernel hQ heq hz).2.2

end BilinearGramian.Kernel

open BilinearGramian.Kernel

theorem solution {n m p : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) :
    (∀ P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → ReachGramianEq A N B P →
      ∀ (u : ℝ → Fin m → ℝ) (x : ℝ → Fin n → ℝ), IsInput u → IsSolution A N B u 0 x →
        ∀ t : ℝ, 0 ≤ t → x t ∈ LinearMap.range (Matrix.toLin' P)) ∧
    (∀ Q : Matrix (Fin n) (Fin n) ℝ, Q.PosSemidef → ObsGramianEq A N C Q →
      ∀ x0 : Fin n → ℝ, x0 ∈ LinearMap.ker (Matrix.toLin' Q) →
        ∀ (u : ℝ → Fin m → ℝ) (x : ℝ → Fin n → ℝ), IsInput u → IsHomSolution A N u x0 x →
          ∀ t : ℝ, 0 ≤ t → C *ᵥ x t = 0) := by
  exact BilinearGramian.Kernel.theorem_3_1 A N B C
