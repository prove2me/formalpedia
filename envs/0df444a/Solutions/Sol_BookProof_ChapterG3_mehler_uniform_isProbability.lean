-- Prove2me | solution 1 for BookProof.ChapterG3.mehler_uniform_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-03T15:16:26.298554+00:00
-- url     : https://prove2.me/submissions/6cbd8f29-aa13-4930-bbf0-d0cf1f139d49

-- Generated from ChapterG3.lean — solution of BookProof.ChapterG3.mehler_uniform_isProbability
import Mathlib
import Definitions.Def_ChapterG3
import Definitions.Def_ChapterG3Promoted
open BookProof.ChapterG3



open MeasureTheory Set Filter
open scoped ENNReal Topology



variable {X : Type*}

variable {X : Type*}

noncomputable section

namespace PhysHSGaussian

/- Inlined from the unpublished `PhysHSGaussian` bundle (platform-world rule:
an unpublished dep cannot be imported). -/
/-- Standard Gaussian on `EuclideanSpace ℝ (Fin k)`. -/
def gaussianE (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (Measure.pi fun _ : Fin k => ProbabilityTheory.gaussianReal 0 1).map
    (MeasurableEquiv.toLp 2 (Fin k → ℝ))

/-- Radial projection onto the sphere of radius `√k` (junk value at 0). -/
def sphereProj (k : ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  if x = 0 then x else (Real.sqrt k / ‖x‖) • x

/-- The uniform measure on the `√k`-sphere. -/
def sphereUniform (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (gaussianE k).map (sphereProj k)

instance gaussianE_isProbability (k : ℕ) : IsProbabilityMeasure (gaussianE k) := by
  constructor ; norm_num [ gaussianE ];
  rw [ Measure.map_apply ] <;> norm_num;
  exact MeasurableEquiv.measurable _

theorem sphereProj_measurable (k : ℕ) : Measurable (sphereProj k) := by
  refine Measurable.piecewise ?_ ?_ ?_;
  · exact MeasurableSingletonClass.measurableSet_singleton _;
  · exact measurable_id;
  · fun_prop

instance sphereUniform_isProbability (k : ℕ) :
    IsProbabilityMeasure (sphereUniform k) := by
  constructor;
  unfold sphereUniform;
  rw [ Measure.map_apply ] <;> norm_num [ sphereProj_measurable ]

theorem sphereUniform_sphere (k : ℕ) (hk : 0 < k) :
    sphereUniform k {x | ‖x‖ = Real.sqrt k} = 1 := by
  -- First show that the normalize map sends almost all vectors to the sphere of radius `√k`.
  have h_norm_map : ∀ᵐ x ∂gaussianE k, ‖sphereProj k x‖ = Real.sqrt k := by
    -- The set of vectors with norm zero has measure zero under the Gaussian measure.
    have h_zero_measure : (gaussianE k) {x : EuclideanSpace ℝ (Fin k) | x = 0} = 0 := by
      simp? [gaussianE];
      rw [ Measure.map_apply ] <;> norm_num [ MeasurableEquiv.toLp ];
      · rw [ MeasureTheory.measure_eq_zero_iff_ae_notMem ] ; norm_num;
        rw [ MeasureTheory.ae_iff ] ; norm_num;
        haveI : NullSingletonClass (ProbabilityTheory.gaussianReal 0 1) :=
          ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
        refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.Measure.pi_hyperplane
          (fun _ => ProbabilityTheory.gaussianReal 0 1) (⟨0, hk⟩ : Fin k) (0 : ℝ))
        intro a ha
        simp only [Set.mem_setOf] at ha ⊢
        have ha1 : WithLp.toLp 2 a = 0 := ha
        have ha' : a = 0 := (WithLp.toLp_eq_zero 2).mp ha1
        rw [ha']; rfl
      · fun_prop;
    filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h_zero_measure ] with x hx;
    unfold sphereProj; simp +decide [ hx, norm_smul, Real.norm_eq_abs ] ;
  -- Apply the fact that the measure of the preimage under a measurable function is equal to the
  -- measure of the set.
  have h_preimage : (gaussianE k).map (sphereProj k) {x | ‖x‖ = Real.sqrt k} = (gaussianE k) {x |
    ‖sphereProj k x‖ = Real.sqrt k} := by
    rw [ Measure.map_apply ] <;> norm_num [ sphereProj_measurable ];
    exact measurableSet_eq_fun ( measurable_norm ) measurable_const |> MeasurableSet.mem;
  have h1 : (gaussianE k) {x | ‖sphereProj k x‖ = Real.sqrt k} = 1 := by
    have h0 : (gaussianE k) {x | ¬ ‖sphereProj k x‖ = Real.sqrt k} = 0 :=
      MeasureTheory.ae_iff.mp h_norm_map
    have hM : MeasurableSet {x : EuclideanSpace ℝ (Fin k) | ‖sphereProj k x‖ = Real.sqrt k} :=
      measurableSet_eq_fun (measurable_norm.comp (sphereProj_measurable k)) measurable_const
    have hfull : (gaussianE k) {x | ‖sphereProj k x‖ = Real.sqrt k} = (gaussianE k) Set.univ := by
      rw [← Set.union_compl_self ({x | ‖sphereProj k x‖ = Real.sqrt k}),
        MeasureTheory.measure_union disjoint_compl_right (MeasurableSet.compl hM),
        Set.compl_ofPred, h0, add_zero]
    rw [hfull, IsProbabilityMeasure.measure_univ]
  show (gaussianE k).map (sphereProj k) {x | ‖x‖ = Real.sqrt k} = 1
  rw [h_preimage, h1]

/-! ### G3. The weight limit -/

theorem weight_tendsto_gaussian (x : ℝ) :
    Filter.Tendsto (fun lam : ℝ => (1 - x^2/lam) ^ (lam - 1/2))
      Filter.atTop (𝓝 (Real.exp (-x^2))) := by
  -- We'll use the fact that $(1 - \frac{x^2}{\lambda})^{\lambda}$ converges to $e^{-x^2}$ as
  -- $\lambda \to \infty$.
  have h_exp : Filter.Tendsto (fun lam => (1 - x^2 / lam) ^ lam) Filter.atTop (nhds (Real.exp
    (-x^2))) := by
    -- We'll use the fact that $(1 + \frac{y}{n})^n$ converges to $e^y$ as $n \to \infty$.
    have h_exp : Filter.Tendsto (fun n => (1 + (-x^2) / n) ^ n) Filter.atTop (nhds (Real.exp
      (-x^2))) := by
      exact Real.tendsto_one_add_div_rpow_exp (-x^2);
    simpa only [ neg_div, sub_eq_add_neg ] using h_exp;
  -- Let's simplify the exponent: $(1 - x^2 / lam)^{lam - 1/2} = (1 - x^2 / lam)^lam * (1 - x^2 /
  -- lam)^{-1/2}$.
  suffices h_simp : Filter.Tendsto (fun lam => ((1 - x^2 / lam) ^ lam) * ((1 - x^2 / lam) ^ (-1 / 2
    : ℝ))) Filter.atTop (nhds (Real.exp (-x^2))) by
    refine h_simp.congr' ?_;
    filter_upwards [ Filter.eventually_gt_atTop ( x ^ 2 ) ] with lam hl
    rw [ ← Real.rpow_add ( sub_pos.mpr ( by rw [ div_lt_iff₀ <| by nlinarith ]; nlinarith ) ) ]
    ring
  have h0 : Filter.Tendsto (fun lam : ℝ => 1 - x ^ 2 / lam) Filter.atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop Filter.tendsto_id)
  have hr : Filter.Tendsto (fun lam : ℝ => (1 - x ^ 2 / lam) ^ (-1 / 2 : ℝ)) Filter.atTop
      (𝓝 ((1 - 0 : ℝ) ^ (-1 / 2 : ℝ))) :=
    Filter.Tendsto.rpow h0 tendsto_const_nhds (Or.inl (by norm_num))
  have hmul : Filter.Tendsto
      (fun lam => ((1 - x ^ 2 / lam) ^ lam) * ((1 - x ^ 2 / lam) ^ (-1 / 2 : ℝ)))
      Filter.atTop (nhds (Real.exp (-x ^ 2) * ((1 : ℝ) - 0) ^ (-1 / 2 : ℝ))) :=
    h_exp.mul hr
  have heq : Real.exp (-x ^ 2) * ((1 - 0 : ℝ) ^ (-1 / 2 : ℝ)) = Real.exp (-x ^ 2) := by norm_num
  rw [← heq]
  exact hmul

/-! ### G5 (continued). Rotation invariance of the uniform sphere measure -/

/-
The radial projection commutes with any linear isometry.
-/
theorem sphereProj_equivariant (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k))
    (x : EuclideanSpace ℝ (Fin k)) :
    sphereProj k (L x) = L (sphereProj k x) := by
  by_cases hx : x = 0 <;> simp +decide [ hx, sphereProj ]

/-
The standard Gaussian on Euclidean space is invariant under linear isometries.
-/
theorem gaussianE_rotation_invariant (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (gaussianE k).map L = gaussianE k := by
  apply MeasureTheory.Measure.ext_of_charFun;
  -- By definition of $gaussianE$, we know that its characteristic function is given by
  -- $\exp(-\|t\|^2 / 2)$.
  have h_char_gaussian : ∀ t : EuclideanSpace ℝ (Fin k), charFun (gaussianE k) t = Complex.exp
    (-‖t‖^2 / 2) := by
    intro t
    unfold gaussianE;
    rw [ charFun ];
    rw [ MeasureTheory.integral_map ];
    · -- The integral of the exponential of the inner product factors as the product of the
      -- componentwise integrals.
      have h_prod : ∫ x : Fin k → ℝ, Complex.exp (Complex.I * ∑ i, x i * t i) ∂Measure.pi (fun _ =>
        ProbabilityTheory.gaussianReal 0 1) = ∏ i, ∫ x : ℝ, Complex.exp (Complex.I * x * t i)
        ∂ProbabilityTheory.gaussianReal 0 1 := by
        have h_prod : ∀ (f : Fin k → ℝ → ℂ), (∫ x : Fin k → ℝ, ∏ i, f i (x i) ∂Measure.pi (fun _ =>
          ProbabilityTheory.gaussianReal 0 1)) = ∏ i, ∫ x : ℝ, f i x ∂ProbabilityTheory.gaussianReal
          0 1 := by
          intro f;
          rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ];
        convert h_prod ( fun i x => Complex.exp ( Complex.I * x * t i ) ) using 3
        norm_num [ Complex.exp_sum, mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ]
      -- The integral of the exponential of the inner product is the product of the integrals of the
      -- exponentials of the components, which is the characteristic function of the Gaussian
      -- measure.
      have h_char : ∀ i : Fin k, ∫ x : ℝ, Complex.exp (Complex.I * x * t i)
        ∂ProbabilityTheory.gaussianReal 0 1 = Complex.exp (-t i ^ 2 / 2) := by
        intro i;
        have := @ProbabilityTheory.charFun_gaussianReal 0 1 ( t i );
        convert this using 1 <;> norm_num [ charFun ]
        · ring_nf
          ac_rfl
        · ring
      convert h_prod using 1;
      · norm_num [ mul_comm, inner ];
      · simp_all? +decide [ EuclideanSpace.norm_eq ];
        norm_cast
        norm_num [ ← Finset.sum_div _ _ _, Real.sq_sqrt <| Finset.sum_nonneg fun _ _ => sq_nonneg _
          ]
        rw [ ← Real.exp_sum ] ; norm_num [ neg_div, Finset.sum_div _ _ _ ];
    · exact Measurable.aemeasurable ( by exact MeasurableEquiv.measurable _ );
    · fun_prop;
  ext t; simp? +decide [ charFun ] ; ring;
  rw [ MeasureTheory.integral_map ];
  · -- Since $L$ is a linear isometry, we have
    -- $\langle L(x), t \rangle = \langle x, L^{-1}(t) \rangle$.
    have h_inner : ∀ x : EuclideanSpace ℝ (Fin k), inner ℝ (L x) t = inner ℝ x (L.symm t) := by
      intro x; exact (by
      rw [ ← L.inner_map_map x ( L.symm t ), L.apply_symm_apply ]);
    have := h_char_gaussian ( L.symm t ) ; simp_all +decide [ charFun ] ;
  · exact L.continuous.aemeasurable;
  · fun_prop (disch := norm_num)

theorem sphereUniform_rotation_invariant (k : ℕ)
    (L : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k)) :
    (sphereUniform k).map L = sphereUniform k := by
  have hcomp : Measure.map ( ⇑L ∘ sphereProj k ) ( gaussianE k )
      = Measure.map ( sphereProj k ∘ ⇑L ) ( gaussianE k ) :=
    congr_arg ( fun f => Measure.map f ( gaussianE k ) )
      ( funext fun x => ( sphereProj_equivariant k L x ).symm )
  calc ( sphereUniform k ).map L
      = Measure.map ( ⇑L ∘ sphereProj k ) ( gaussianE k ) :=
        Measure.map_map L.continuous.measurable ( sphereProj_measurable k )
    _ = Measure.map ( sphereProj k ∘ ⇑L ) ( gaussianE k ) := hcomp
    _ = Measure.map ( sphereProj k ) ( Measure.map ( ⇑L ) ( gaussianE k ) ) :=
        ( Measure.map_map ( sphereProj_measurable k ) L.continuous.measurable ).symm
    _ = sphereUniform k := by rw [ gaussianE_rotation_invariant k L ] ; rfl


end PhysHSGaussian

end

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) :
    IsProbabilityMeasure (PhysHSGaussian.sphereUniform k) := PhysHSGaussian.sphereUniform_isProbability k
