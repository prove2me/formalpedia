-- Prove2me | solution 1 for BregmanPPA.EqMult.theorem6_limit_points
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T19:27:44.578242+00:00
-- url     : https://prove2.me/submissions/a768b916-3371-4ad9-a8fd-165d2b401bd5

import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_EqMult_EqConstrainedProgram
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_fenchelConjugate
set_option autoImplicit false
section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n : ℕ}

theorem original_primal_extension_proper (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f) : IsProperFn (fX X f) := by
  classical
  constructor
  · intro x
    apply EReal.add_ne_bot_iff.mpr
    refine ⟨hP.ne_bot x,?_⟩
    simp only [indicatorE]
    split <;> simp
  · obtain ⟨x,hx,hf⟩ := hP.finite_on_X
    refine ⟨x,?_⟩
    simpa only [fX,indicatorE,if_pos hx,add_zero] using hf

theorem original_primal_extension_convex (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f) : IsConvexFn (fX X f) := by
  classical
  have he (u : EuclideanSpace ℝ (Fin n) × ℝ) :
      fX X f u.1 ≤ (u.2 : EReal) ↔ u.1 ∈ X ∧ f u.1 ≤ (u.2 : EReal) := by
    by_cases hx : u.1 ∈ X
    · simp [fX,indicatorE,hx]
    · simp [fX,indicatorE,hx,EReal.add_top_of_ne_bot (hP.ne_bot u.1),top_le_iff]
  intro u hu v hv a b ha hb hab
  change fX X f u.1 ≤ (u.2 : EReal) at hu
  change fX X f v.1 ≤ (v.2 : EReal) at hv
  change fX X f (a • u+b • v).1 ≤ ((a • u+b • v).2 : EReal)
  rw [he] at hu hv ⊢
  exact ⟨hP.convex hu.1 hv.1 ha hb hab,hP.convexFn hu.2 hv.2 ha hb hab⟩
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n : ℕ}

theorem original_primal_extension_lsc (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f) :
    LowerSemicontinuous (fX X f) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro a
  by_cases ha : a=⊤
  · subst a; simp
  have he : (fX X f) ⁻¹' Set.Iic a = X ∩ f ⁻¹' Set.Iic a := by
    ext x
    by_cases hx : x ∈ X
    · simp [fX,indicatorE,hx]
    · simp [fX,indicatorE,hx,EReal.add_top_of_ne_bot (hP.ne_bot x),top_le_iff,ha]
  rw [he]
  exact hP.closed.inter (lowerSemicontinuous_iff_isClosed_preimage.mp hP.lsc a)

theorem original_subgradient_graph_limit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (F : H → EReal) (hp : IsProperFn F)
    (hl : LowerSemicontinuous F) (zseq gseq : ℕ → H) (z g : H)
    (hz : Tendsto zseq atTop (𝓝 z)) (hg : Tendsto gseq atTop (𝓝 g))
    (hs : ∀ k, IsSubgradient F (zseq k) (gseq k)) : IsSubgradient F z g := by
  have hbound (y : H) (hy : F y ≠ ⊤) :
      F z ≤ (((F y).toReal-inner ℝ g (y-z) : ℝ) : EReal) := by
    have ey := EReal.coe_toReal hy (hp.1 y)
    have ht : Tendsto (fun k => (F y).toReal-inner ℝ (gseq k) (y-zseq k)) atTop
        (𝓝 ((F y).toReal-inner ℝ g (y-z))) :=
      tendsto_const_nhds.sub (hg.inner (tendsto_const_nhds.sub hz))
    have he := (continuous_coe_real_ereal.tendsto _).comp ht
    change (z,(((F y).toReal-inner ℝ g (y-z) : ℝ) : EReal)) ∈ {p : H × EReal | F p.1 ≤ p.2}
    apply hl.isClosed_epigraph.mem_of_tendsto (hz.prodMk_nhds he)
    apply Eventually.of_forall
    intro k
    have hi := (hs k).2 y
    have ek := EReal.coe_toReal (hs k).1 (hp.1 (zseq k))
    rw [← ek,← ey,← EReal.coe_add] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    change F (zseq k) ≤ (((F y).toReal-inner ℝ (gseq k) (y-zseq k) : ℝ) : EReal)
    rw [← ek]
    apply EReal.coe_le_coe_iff.mpr
    linarith
  have hzt : F z ≠ ⊤ := by
    obtain ⟨y,hy⟩ := hp.2
    exact ne_of_lt ((hbound y hy).trans_lt (EReal.coe_lt_top _))
  refine ⟨hzt,?_⟩
  intro y
  by_cases hy : F y=⊤
  · rw [hy]; exact le_top
  have hb := hbound y hy
  have ez := EReal.coe_toReal hzt (hp.1 z)
  have ey := EReal.coe_toReal hy (hp.1 y)
  rw [← ez] at hb
  have hbr := EReal.coe_le_coe_iff.mp hb
  rw [← ez,← ey,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  linarith
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- First-order support at a point in the original open zone, including boundary test points. -/
theorem gradient_support (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {y z : H} (hy : y ∈ S) (hz : z ∈ closure S) :
    inner ℝ (gradient h y) (z-y) ≤ h z-h y := by
  have hd : DifferentiableAt ℝ h y :=
    ((hh.contDiffOn.differentiableOn (by simp)) y hy).differentiableAt (hh.isOpen.mem_nhds hy)
  let l : ℝ →ᵃ[ℝ] H := AffineMap.lineMap y z
  have hcv := hh.strictConvexOn.convexOn.comp_affineMap l
  have h0 : (0 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using subset_closure hy
  have h1 : (1 : ℝ) ∈ l ⁻¹' closure S := by simpa [l] using hz
  have hder : HasDerivAt (h ∘ l) (fderiv ℝ h y (z-y)) 0 := by
    apply hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap (a := y) (b := z) (x := (0 : ℝ)))
    simp [l]
  have hs := hcv.le_slope_of_hasDerivAt h0 h1 (by norm_num) hder
  simpa [l,slope,inner_gradient_left] using hs

theorem bregman_nonneg (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {x y : H} (hx : x ∈ closure S) (hy : y ∈ S) : 0 ≤ bregmanD h x y := by
  have hs := gradient_support S h hh hy hx
  dsimp [bregmanD]; linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open ConvexOptimization
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem conjugate_at_gradient (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (x : EuclideanSpace ℝ (Fin m)) :
    fenchelConjugate h (gradient h x)=((inner ℝ x (gradient h x)-h x : ℝ) : EReal) := by
  apply le_antisymm
  · apply iSup_le
    intro z
    apply EReal.coe_le_coe_iff.mpr
    have hs := BregmanPPACodex.gradient_support Set.univ h hh
      (y := x) (z := z) (by trivial) (by simp)
    rw [inner_sub_right,real_inner_comm] at hs
    have hc : inner ℝ (gradient h x) x=inner ℝ x (gradient h x) := real_inner_comm _ _
    rw [hc] at hs
    linarith
  · exact le_iSup_of_le x le_rfl

theorem conjugate_finite (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) (w : EuclideanSpace ℝ (Fin m)) :
    fenchelConjugate h w ≠ ⊥ ∧ fenchelConjugate h w ≠ ⊤ := by
  obtain ⟨x,rfl⟩ := him w
  rw [conjugate_at_gradient h hh x]
  exact ⟨EReal.coe_ne_bot _,EReal.coe_ne_top _⟩
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open ConvexOptimization
namespace BregmanEqMultCodex
variable {m : ℕ}

noncomputable def conjugate_real (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (w : EuclideanSpace ℝ (Fin m)) : ℝ := (fenchelConjugate h w).toReal

theorem conjugate_real_at_gradient (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (x : EuclideanSpace ℝ (Fin m)) :
    conjugate_real h (gradient h x)=inner ℝ x (gradient h x)-h x := by
  simp only [conjugate_real,conjugate_at_gradient h hh x,EReal.toReal_coe]

theorem conjugate_real_bound (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) (x w : EuclideanSpace ℝ (Fin m)) :
    inner ℝ x w-h x ≤ conjugate_real h w := by
  obtain ⟨z,rfl⟩ := him w
  have he : ((inner ℝ x (gradient h z)-h x : ℝ) : EReal) ≤
      fenchelConjugate h (gradient h z) := le_iSup_of_le x le_rfl
  rw [conjugate_at_gradient h hh z] at he
  rw [conjugate_real_at_gradient h hh z]
  exact EReal.coe_le_coe_iff.mp he

theorem conjugate_real_convex (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) : ConvexOn ℝ Set.univ (conjugate_real h) := by
  refine ⟨convex_univ,?_⟩
  intro u _ v _ a b ha hb hab
  obtain ⟨z,hz⟩ := him (a • u+b • v)
  have he : conjugate_real h (a • u+b • v)=inner ℝ z (a • u+b • v)-h z := by
    rw [← hz,conjugate_real_at_gradient h hh z]
  have h1 := conjugate_real_bound h hh him z u
  have h2 := conjugate_real_bound h hh him z v
  have ha1 := mul_le_mul_of_nonneg_left h1 ha
  have hb2 := mul_le_mul_of_nonneg_left h2 hb
  rw [he,inner_add_right,inner_smul_right,inner_smul_right]
  simp only [smul_eq_mul]
  nlinarith [show (a+b)*h z=h z by rw [hab,one_mul]]

theorem conjugate_real_continuous (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) : Continuous (conjugate_real h) := by
  exact continuousOn_univ.mp ((conjugate_real_convex h hh him).continuousOn isOpen_univ)
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem inverse_gradient_local_bound (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w₀ : EuclideanSpace ℝ (Fin m)) :
    ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ x : EuclideanSpace ℝ (Fin m),
      gradient h x ∈ Metric.ball w₀ δ → ‖x‖ ≤ R := by
  have ht := (conjugate_real_continuous h hh him).continuousAt.tendsto (x := w₀)
  have hb : ∀ᶠ w in 𝓝 w₀, conjugate_real h w < conjugate_real h w₀+1 :=
    ht.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hb
  obtain ⟨R,hR,hbound⟩ := (hh.bounded_L₂ (h 0+conjugate_real h w₀+1) 0 (by simp)).exists_pos_norm_le
  refine ⟨δ,R,hδ,hR,?_⟩
  intro x hx
  apply hbound x
  refine ⟨by trivial,?_⟩
  have he : bregmanD h 0 x=h 0+conjugate_real h (gradient h x) := by
    rw [conjugate_real_at_gradient h hh x]
    simp only [bregmanD,zero_sub,inner_neg_right]
    rw [real_inner_comm]
    ring
  rw [he]
  have hb' : conjugate_real h (gradient h x) < conjugate_real h w₀+1 := hball hx
  linarith
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open BregmanPPA.Convergence
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem original_gradient_injective (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) : Function.Injective (gradient h) := by
  intro x y hxy
  let F : EuclideanSpace ℝ (Fin m) → ℝ := fun z => h z-inner ℝ (gradient h x) z
  have hs : StrictConvexOn ℝ Set.univ h := by simpa only [closure_univ] using hh.strictConvexOn
  have hl : ConcaveOn ℝ Set.univ (fun z => inner ℝ (gradient h x) z) := by
    refine ⟨convex_univ,?_⟩
    intro u _ v _ a b _ _ _
    simp only [inner_add_right,inner_smul_right,smul_eq_mul]
    exact le_rfl
  have hf : StrictConvexOn ℝ Set.univ F := hs.sub_concaveOn hl
  have hx : IsMinOn F Set.univ x := by
    intro z _
    have hi := BregmanPPACodex.gradient_support Set.univ h hh
      (y := x) (z := z) (by trivial) (by simp)
    rw [inner_sub_right] at hi
    dsimp [F]; linarith
  have hy : IsMinOn F Set.univ y := by
    intro z _
    have hi := BregmanPPACodex.gradient_support Set.univ h hh
      (y := y) (z := z) (by trivial) (by simp)
    rw [← hxy,inner_sub_right] at hi
    dsimp [F]; linarith
  exact hf.eq_of_isMinOn hx hy (by trivial) (by trivial)

noncomputable def inverse_gradient (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (him : Function.Surjective (gradient h)) (w : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) := Classical.choose (him w)

theorem gradient_inverse (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (him : Function.Surjective (gradient h)) (w : EuclideanSpace ℝ (Fin m)) :
    gradient h (inverse_gradient h him w)=w := Classical.choose_spec (him w)

theorem inverse_gradient_gradient (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (x : EuclideanSpace ℝ (Fin m)) : inverse_gradient h him (gradient h x)=x :=
  original_gradient_injective h hh (gradient_inverse h him (gradient h x))
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem three_point_identity (h : H → ℝ) (v y p : H) :
    bregmanD h v y-bregmanD h v p-bregmanD h p y =
      inner ℝ (p-v) (gradient h y-gradient h p) := by
  have he : v-y = (v-p)+(p-y) := by abel
  have hi : inner ℝ (gradient h y) (v-y) =
      inner ℝ (gradient h y) (v-p)+inner ℝ (gradient h y) (p-y) := by
    rw [he,inner_add_right]
  have hc1 : inner ℝ (p-v) (gradient h y) = inner ℝ (gradient h y) (p-v) :=
    real_inner_comm _ _
  have hc2 : inner ℝ (p-v) (gradient h p) = inner ℝ (gradient h p) (p-v) :=
    real_inner_comm _ _
  rw [inner_sub_right,hc1,hc2,← neg_sub v p,inner_neg_right,inner_neg_right]
  dsimp [bregmanD]
  linarith

theorem weighted_graph_comparison (T : H → Set H) (h : H → ℝ) (hT : IsMonotoneOp T)
    (v w y p : H) (c : ℝ) (hc : 0 < c) (hw : w ∈ T v)
    (hp : c⁻¹ • (gradient h y-gradient h p) ∈ T p) :
    c*inner ℝ w (p-v) ≤ bregmanD h v y-bregmanD h v p-bregmanD h p y := by
  have hm := hT p v _ w hp hw
  rw [inner_sub_right,inner_smul_right] at hm
  change 0 ≤ c⁻¹*inner ℝ (p-v) (gradient h y-gradient h p)-inner ℝ (p-v) w at hm
  have hm' : inner ℝ (p-v) w ≤ c⁻¹*inner ℝ (p-v) (gradient h y-gradient h p) := by linarith
  have ht := mul_le_mul_of_nonneg_left hm' hc.le
  simp only [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul] at ht
  rw [three_point_identity]
  have he : inner ℝ (p-v) w = inner ℝ w (p-v) := real_inner_comm _ _
  rwa [he] at ht

theorem weighted_descent (T : H → Set H) (h : H → ℝ) (hT : IsMonotoneOp T)
    (z y p : H) (c : ℝ) (hc : 0 < c) (hz : z ∈ zer T)
    (hp : c⁻¹ • (gradient h y-gradient h p) ∈ T p) :
    bregmanD h z p ≤ bregmanD h z y-bregmanD h p y := by
  have ht := weighted_graph_comparison T h hT z 0 y p c hc hz hp
  simp only [inner_zero_left,mul_zero] at ht
  linarith
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem zero_mem_closure (T : H → Set H) (S : Set H) (hdom : dom T ⊆ closure S)
    {z : H} (hz : z ∈ zer T) : z ∈ closure S := hdom ⟨0,hz⟩

theorem run_descent (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (z : H) (hz : z ∈ zer T) (k : ℕ) :
    bregmanD h z (x (k+1)) ≤ bregmanD h z (x k)-bregmanD h (x (k+1)) (x k) :=
  weighted_descent T h hT z (x k) (x (k+1)) (c k) (hc k) hz (hx k).2

theorem distance_antitone (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h)
    (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    Antitone (fun k => bregmanD h z (x k)) := by
  apply antitone_nat_of_succ_le
  intro k
  have hd := run_descent T S h c x hT hc hx z hz k
  have hn := bregman_nonneg S h hh (subset_closure (hx (k+1)).1) (hx k).1
  linarith

theorem step1 (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    (∀ k, bregmanD h z (x (k+1)) ≤ bregmanD h z (x k)-bregmanD h (x (k+1)) (x k)) ∧
    (∃ δ : ℝ, 0 ≤ δ ∧ Tendsto (fun k => bregmanD h z (x k)) atTop (𝓝 δ)) ∧
    Bornology.IsBounded (Set.range x) := by
  have hzc := zero_mem_closure T S hdom hz
  have hnonneg (k : ℕ) : 0 ≤ bregmanD h z (x k) := bregman_nonneg S h hh hzc (hx k).1
  have hanti := distance_antitone T S h c x hT.1 hh hc hx z hz
  have hbelow : BddBelow (Set.range (fun k => bregmanD h z (x k))) := by
    refine ⟨0, ?_⟩; rintro _ ⟨k,rfl⟩; exact hnonneg k
  have ht := tendsto_atTop_ciInf hanti hbelow
  have hδ : 0 ≤ ⨅ k, bregmanD h z (x k) :=
    (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto ht
      (Eventually.of_forall hnonneg)
  refine ⟨run_descent T S h c x hT.1 hc hx z hz,⟨_,hδ,ht⟩, ?_⟩
  apply (hh.bounded_L₂ (bregmanD h z (x 0)) z hzc).subset
  rintro _ ⟨k,rfl⟩
  exact ⟨(hx k).1,hanti (Nat.zero_le k)⟩
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology Finset
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem step_distance_sum (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x)
    (z : H) (hz : z ∈ zer T) (N : ℕ) :
    (∑ k ∈ range N, bregmanD h (x (k+1)) (x k))+bregmanD h z (x N) ≤ bregmanD h z (x 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ]
    have hd := run_descent T S h c x hT hc hx z hz N
    linarith

theorem step_distance_zero (T : H → Set H) (S : Set H) (h : H → ℝ) (c : ℕ → ℝ) (x : ℕ → H)
    (hT : IsMonotoneOp T) (hh : IsBregmanFunction S h) (hdom : dom T ⊆ closure S)
    (hc : ∀ k, 0 < c k) (hx : IsBregmanPPARun S h T c x) (z : H) (hz : z ∈ zer T) :
    Tendsto (fun k => bregmanD h (x (k+1)) (x k)) atTop (𝓝 0) := by
  have hzc := zero_mem_closure T S hdom hz
  have hs : Summable (fun k => bregmanD h (x (k+1)) (x k)) := by
    apply summable_of_sum_range_le
      (fun k => bregman_nonneg S h hh (subset_closure (hx (k+1)).1) (hx k).1)
      (c := bregmanD h z (x 0))
    intro N
    have hsum := step_distance_sum T S h c x hT hc hx z hz N
    have hn := bregman_nonneg S h hh hzc (hx N).1
    linarith
  exact hs.tendsto_atTop_zero

theorem successor_subsequence_limit (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hz : (zer T).Nonempty) (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : H)
    (hlim : Tendsto (x ∘ φ) atTop (𝓝 p)) :
    Tendsto (fun k => x (φ k+1)) atTop (𝓝 p) := by
  obtain ⟨z,hz⟩ := hz
  have hb := (step1 T S h c x hT hh hdom hc hcinf hx z hz).2.2
  have hfirst : Bornology.IsBounded (Set.range (fun k => x (φ k+1))) := hb.subset (by
    rintro _ ⟨k,rfl⟩; exact ⟨φ k+1,rfl⟩)
  have hpc : p ∈ closure S := isClosed_closure.mem_of_tendsto hlim
    (Eventually.of_forall (fun k => subset_closure (hx (φ k)).1))
  have hD : Tendsto (fun k => bregmanD h (x (φ k+1)) ((x ∘ φ) k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (step_distance_zero T S h c x hT.1 hh hdom hc hx z hz).comp hφ.tendsto_atTop
  exact hh.tendsto_of_zero (fun k => x (φ k+1)) (x ∘ φ) p
    (fun k => subset_closure (hx (φ k+1)).1) (fun k => (hx (φ k)).1)
    hlim hpc hfirst hD
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Adjoining a related point to the exact original graph cannot extend a maximal operator. -/
theorem maximal_related_point (T : H → Set H) (hT : IsMaximalMonotone T) (z u : H)
    (hrel : ∀ v w : H, w ∈ T v → 0 ≤ inner ℝ (z-v) (u-w)) : u ∈ T z := by
  let U : H → Set H := fun x => T x ∪ {v | x=z ∧ v=u}
  have hU : IsMonotoneOp U := by
    intro x y v w hv hw
    rcases hv with hv | ⟨hx,hv⟩
    · rcases hw with hw | ⟨hy,hw⟩
      · exact hT.1 x y v w hv hw
      · rw [hy,hw]
        have he : inner ℝ (x-z) (v-u) = inner ℝ (z-x) (u-v) := by
          rw [← neg_sub z x,← neg_sub u v,inner_neg_left,inner_neg_right,neg_neg]
        rw [he]; exact hrel x v hv
    · rcases hw with hw | ⟨hy,hw⟩
      · rw [hx,hv]; exact hrel y w hw
      · rw [hx,hv,hy,hw]; simp
  have hEq : U=T := hT.2 U hU (fun x => Set.subset_union_left)
  have hu : u ∈ U z := Or.inr ⟨rfl,rfl⟩
  rwa [hEq] at hu

/-- Norm limits of graph points remain in the exact original maximal monotone graph. -/
theorem maximal_graph_limit (T : H → Set H) (hT : IsMaximalMonotone T)
    (x u : ℕ → H) (z v : H) (hx : Tendsto x atTop (𝓝 z)) (hu : Tendsto u atTop (𝓝 v))
    (hmem : ∀ k, u k ∈ T (x k)) : v ∈ T z := by
  apply maximal_related_point T hT z v
  intro y w hw
  have ht : Tendsto (fun k => inner ℝ (x k-y) (u k-w)) atTop (𝓝 (inner ℝ (z-y) (v-w))) :=
    (hx.sub_const y).inner (hu.sub_const w)
  exact (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ))).mem_of_tendsto ht
    (Eventually.of_forall (fun k => hT.1 (x k) y (u k) w (hmem k) hw))
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology
namespace BregmanPPACodex
open BregmanPPA.Convergence ThreeOpSplitting.Convergence
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

theorem gradient_continuous_in_zone (S : Set H) (h : H → ℝ) (hh : IsBregmanFunction S h)
    {p : H} (hp : p ∈ S) : ContinuousAt (gradient h) p := by
  have hf := (hh.contDiffOn.contDiffAt (hh.isOpen.mem_nhds hp)).continuousAt_fderiv (by simp)
  change ContinuousAt (fun y => (InnerProductSpace.toDual ℝ H).symm (fderiv ℝ h y)) p
  simpa only [Function.comp_def] using
    (InnerProductSpace.toDual ℝ H).symm.continuous.continuousAt.comp hf

theorem bounded_inverse_residual (a : ℕ → H) (c : ℕ → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hc : ∀ k, 0 < c k) (hle : ∀ k, ε ≤ c k)
    (ha : Tendsto a atTop (𝓝 0)) : Tendsto (fun k => (c k)⁻¹ • a k) atTop (𝓝 0) := by
  have hbound (k : ℕ) : ‖(c k)⁻¹ • a k‖ ≤ ‖a k‖/ε := by
    rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr (hc k)).le]
    simpa only [div_eq_mul_inv,mul_comm] using
      div_le_div_of_nonneg_left (norm_nonneg (a k)) hε (hle k)
  have ht : Tendsto (fun k => ‖a k‖/ε) atTop (𝓝 0) := by simpa using ha.norm.div_const ε
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun k => norm_nonneg _) hbound ht)

theorem interior_cluster_zero (T : H → Set H) (S : Set H) (h : H → ℝ)
    (c : ℕ → ℝ) (x : ℕ → H) (hT : IsMaximalMonotone T) (hh : IsBregmanFunction S h)
    (hdom : dom T ⊆ closure S) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) (hx : IsBregmanPPARun S h T c x)
    (hz : (zer T).Nonempty) (hC1 : closure (dom T) ⊆ S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (p : H) (hlim : Tendsto (x ∘ φ) atTop (𝓝 p)) :
    p ∈ zer T := by
  have hnext := successor_subsequence_limit T S h c x hT hh hdom hc hcinf hx hz φ hφ p hlim
  have hpdom : p ∈ closure (dom T) := isClosed_closure.mem_of_tendsto hnext
    (Eventually.of_forall (fun k => subset_closure ⟨_,(hx (φ k)).2⟩))
  have hgrad := (gradient_continuous_in_zone S h hh (hC1 hpdom)).tendsto
  have hdiff : Tendsto (fun k => gradient h (x (φ k))-gradient h (x (φ k+1))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self] using (hgrad.comp hlim).sub (hgrad.comp hnext)
  obtain ⟨ε,hε,hle⟩ := hcinf
  have hres := bounded_inverse_residual _ (c ∘ φ) ε hε (fun k => hc (φ k))
    (fun k => hle (φ k)) hdiff
  exact maximal_graph_limit T hT (fun k => x (φ k+1))
    (fun k => (c (φ k))⁻¹ • (gradient h (x (φ k))-gradient h (x (φ k+1)))) p 0
    hnext hres (fun k => (hx (φ k)).2)
end BregmanPPACodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem inverse_gradient_continuous (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h)) :
    Continuous (inverse_gradient h him) := by
  apply continuous_iff_continuousAt.mpr
  intro w₀
  obtain ⟨δ,R,hδ,_,hbound⟩ := inverse_gradient_local_bound h hh him w₀
  change Tendsto (inverse_gradient h him) (𝓝 w₀) (𝓝 (inverse_gradient h him w₀))
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) R).tendsto_nhds_of_unique_mapClusterPt
  · filter_upwards [Metric.isOpen_ball.mem_nhds (show w₀ ∈ Metric.ball w₀ δ by
        simpa only [Metric.mem_ball,dist_self] using hδ)] with w hw
    rw [Metric.mem_closedBall,dist_zero_right]
    apply hbound (inverse_gradient h him w)
    rwa [gradient_inverse]
  · intro x _ hx
    have hg := (BregmanPPACodex.gradient_continuous_in_zone Set.univ h hh
      (p := x) (by trivial)).tendsto
    have hc := hx.tendsto_comp hg
    have hid : gradient h ∘ inverse_gradient h him=id := funext (gradient_inverse h him)
    rw [hid] at hc
    have he : gradient h x=w₀ := eq_of_nhds_neBot (by
      simpa only [MapClusterPt,Filter.map_id,ClusterPt] using hc)
    apply original_gradient_injective h hh
    rwa [gradient_inverse]
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence
namespace BregmanEqMultCodex
variable {m : ℕ}

theorem conjugate_inverse_value (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w : EuclideanSpace ℝ (Fin m)) :
    conjugate_real h w=inner ℝ (inverse_gradient h him w) w-h (inverse_gradient h him w) := by
  have he := conjugate_real_at_gradient h hh (inverse_gradient h him w)
  rwa [gradient_inverse] at he

theorem conjugate_support (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w v : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (inverse_gradient h him w) (v-w) ≤ conjugate_real h v-conjugate_real h w := by
  have hb := conjugate_real_bound h hh him (inverse_gradient h him w) v
  rw [conjugate_inverse_value h hh him w,inner_sub_right]
  linarith

theorem conjugate_hasFDerivAt (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (conjugate_real h) ((InnerProductSpace.toDual ℝ _) (inverse_gradient h him w)) w := by
  apply hasFDerivAt_iff_isLittleO.mpr
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  have hj : Tendsto (inverse_gradient h him) (𝓝 w) (𝓝 (inverse_gradient h him w)) :=
    (inverse_gradient_continuous h hh him).continuousAt.tendsto
  have ht : Tendsto (fun v => ‖inverse_gradient h him v-inverse_gradient h him w‖)
      (𝓝 w) (𝓝 0) := by
    simpa only [sub_self,norm_zero] using
      (hj.sub_const (inverse_gradient h him w)).norm
  filter_upwards [ht.eventually (Iio_mem_nhds hε)] with v hv
  have hl := conjugate_support h hh him w v
  have hu := conjugate_support h hh him v w
  rw [← neg_sub v w,inner_neg_right] at hu
  have hp : 0 ≤ conjugate_real h v-conjugate_real h w-inner ℝ (inverse_gradient h him w) (v-w) := by
    linarith
  have hb : conjugate_real h v-conjugate_real h w-inner ℝ (inverse_gradient h him w) (v-w) ≤
      inner ℝ (inverse_gradient h him v-inverse_gradient h him w) (v-w) := by
    rw [inner_sub_left]; linarith
  simp only [InnerProductSpace.toDual_apply_apply]
  rw [Real.norm_of_nonneg hp]
  exact hb.trans ((real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hv.le (norm_nonneg _)))

theorem gradient_conjugate_inverse (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (w : EuclideanSpace ℝ (Fin m)) :
    gradient (conjugate_real h) w=inverse_gradient h him w := by
  have hd := (conjugate_hasFDerivAt h hh him w).fderiv
  change (InnerProductSpace.toDual ℝ _).symm (fderiv ℝ (conjugate_real h) w)=_
  rw [hd]
  exact (InnerProductSpace.toDual ℝ _).symm_apply_apply _
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB
namespace BregmanEqMultCodex
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Necessary subgradient condition for the original extended-real convex objective. -/
theorem convex_smooth_min_subgradient (F : H → EReal) (hp : IsProperFn F)
    (hc : IsConvexFn F) (G : H → ℝ) (z g : H)
    (hd : HasFDerivAt G ((InnerProductSpace.toDual ℝ H) g) z)
    (hmin : ∀ y, F z+(G z : EReal) ≤ F y+(G y : EReal)) :
    IsSubgradient F z (-g) := by
  have hz : F z ≠ ⊤ := by
    obtain ⟨y,hy⟩ := hp.2
    have hey := EReal.coe_toReal hy (hp.1 y)
    intro hzt
    have hm := hmin y
    rw [hzt,EReal.top_add_coe,← hey,← EReal.coe_add] at hm
    exact EReal.coe_ne_top _ (top_le_iff.mp hm)
  refine ⟨hz,?_⟩
  intro y
  by_cases hy : F y=⊤
  · rw [hy]; exact le_top
  have ez := EReal.coe_toReal hz (hp.1 z)
  have ey := EReal.coe_toReal hy (hp.1 y)
  rw [← ez,← ey,← EReal.coe_add]
  apply EReal.coe_le_coe_iff.mpr
  let l : ℝ →ᵃ[ℝ] H := AffineMap.lineMap z y
  have hder : HasDerivAt (G ∘ l) (inner ℝ g (y-z)) 0 := by
    simpa only [l,InnerProductSpace.toDual_apply_apply] using
      hd.comp_hasDerivAt_of_eq (0 : ℝ)
        (AffineMap.hasDerivAt_lineMap (a := z) (b := y) (x := (0 : ℝ))) (by simp)
  have hb : ∀ t : ℝ, 0 < t → t < 1 →
      (F z).toReal-(F y).toReal ≤ t⁻¹*(G (l t)-G z) := by
    intro t ht ht1
    have hez : (z,(F z).toReal) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      change F z ≤ ((F z).toReal : EReal); rw [ez]
    have hey : (y,(F y).toReal) ∈ {p : H × ℝ | F p.1 ≤ (p.2 : EReal)} := by
      change F y ≤ ((F y).toReal : EReal); rw [ey]
    have hcv := hc hez hey (show 0 ≤ 1-t by linarith) ht.le (show (1-t)+t=1 by ring)
    change F ((1-t) • z+t • y) ≤ (((1-t)*(F z).toReal+t*(F y).toReal : ℝ) : EReal) at hcv
    have hl : l t=(1-t) • z+t • y := by simp [l,AffineMap.lineMap_apply_module]
    rw [← hl] at hcv
    have hft : F (l t) ≠ ⊤ := ne_of_lt (hcv.trans_lt (EReal.coe_lt_top _))
    have eft := EReal.coe_toReal hft (hp.1 (l t))
    have hm := hmin (l t)
    rw [← ez,← eft,← EReal.coe_add,← EReal.coe_add] at hm
    have hmr := EReal.coe_le_coe_iff.mp hm
    rw [← eft] at hcv
    have hcvr := EReal.coe_le_coe_iff.mp hcv
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ ht).mpr
    change ((F z).toReal-(F y).toReal)*t ≤ G (l t)-G z
    nlinarith
  have hs := hder.tendsto_slope_zero_right
  have hlow : (F z).toReal-(F y).toReal ≤ inner ℝ g (y-z) := by
    apply ge_of_tendsto hs
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    simpa only [l,Function.comp_def,zero_add,smul_eq_mul,AffineMap.lineMap_apply_zero] using hb t ht ht1
  rw [inner_neg_left]
  linarith
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.Convergence BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n m : ℕ}

noncomputable def augmented_cost
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b p : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (c : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
    c⁻¹*conjugate_real h (gradient h p+c • (A z-b))

theorem augmented_cost_hasFDerivAt
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b p : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (c : ℝ) (hc : 0 < c) (z : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (augmented_cost A b p h c)
      ((InnerProductSpace.toDual ℝ _) (ContinuousLinearMap.adjoint A
        (inverse_gradient h him (gradient h p+c • (A z-b))))) z := by
  let w := gradient h p+c • (A z-b)
  have hi : HasFDerivAt (fun y => gradient h p+c • (A y-b)) (c • A) z :=
    ((A.hasFDerivAt.sub_const b).const_smul c).const_add (gradient h p)
  have hd := ((conjugate_hasFDerivAt h hh him w).comp z hi).const_mul c⁻¹
  have he : c⁻¹ • (((InnerProductSpace.toDual ℝ _) (inverse_gradient h him w)).comp (c • A)) =
      (InnerProductSpace.toDual ℝ _) (ContinuousLinearMap.adjoint A (inverse_gradient h him w)) := by
    ext v
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      smul_eq_mul,InnerProductSpace.toDual_apply_apply,inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
    rw [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]
  rw [he] at hd
  exact hd

theorem original_primal_subgradient
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (k : ℕ) :
    -(ContinuousLinearMap.adjoint A (p (k+1))) ∈ subdiffOp (fX X f) (x (k+1)) := by
  classical
  let G := augmented_cost A b (p k) h (c k)
  have hx := (hrun k).1
  have hmin : ∀ y, fX X f (x (k+1))+(G (x (k+1)) : EReal) ≤ fX X f y+(G y : EReal) := by
    intro y
    by_cases hy : y ∈ X
    · simpa only [fX,indicatorE,if_pos hx,if_pos hy,add_zero,G,augmented_cost,
        conjugate_real,EReal.toReal_mul,EReal.toReal_coe] using (hrun k).2.1 y hy
    · simp only [fX,indicatorE,if_neg hy,EReal.add_top_of_ne_bot (hP.ne_bot y),EReal.top_add_coe]
      exact le_top
  have hd := augmented_cost_hasFDerivAt A b (p k) h hh him (c k) (hc k) (x (k+1))
  have he := (hrun k).2.2
  change p (k+1)=gradient (conjugate_real h) _ at he
  rw [gradient_conjugate_inverse h hh him] at he
  rw [← he] at hd
  exact convex_smooth_min_subgradient (fX X f) (original_primal_extension_proper X f hP)
    (original_primal_extension_convex X f hP) G (x (k+1))
    (ContinuousLinearMap.adjoint A (p (k+1))) hd hmin
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n m : ℕ}

theorem original_gradient_update
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (k : ℕ) :
    gradient h (p (k+1))-gradient h (p k)=c k • (A (x (k+1))-b) := by
  have he := (hrun k).2.2
  change p (k+1)=gradient (conjugate_real h) _ at he
  rw [gradient_conjugate_inverse h hh him] at he
  rw [he,gradient_inverse]
  abel

theorem original_asymptotic_feasibility
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    (hh : IsBregmanFunction Set.univ h) (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (pstar : EuclideanSpace ℝ (Fin m))
    (hp : Tendsto p atTop (𝓝 pstar)) : Tendsto (fun k => A (x k)) atTop (𝓝 b) := by
  have hg := (BregmanPPACodex.gradient_continuous_in_zone Set.univ h hh
    (p := pstar) (by trivial)).tendsto
  have hgp := hg.comp hp
  have hdiff : Tendsto (fun k => gradient h (p (k+1))-gradient h (p k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self] using
      (hgp.comp (tendsto_add_atTop_nat 1)).sub hgp
  obtain ⟨ε,hε,hle⟩ := hcinf
  have hr := BregmanPPACodex.bounded_inverse_residual _ c ε hε hc hle hdiff
  have he (k : ℕ) : (c k)⁻¹ • (gradient h (p (k+1))-gradient h (p k))=A (x (k+1))-b := by
    rw [original_gradient_update A b X f h hh him c x p hrun k,
      smul_smul,inv_mul_cancel₀ (hc k).ne',one_smul]
  simp_rw [he] at hr
  have hs : Tendsto (fun k => A (x (k+1))) atTop (𝓝 b) := by
    simpa only [sub_add_cancel,zero_add] using hr.add_const b
  exact (tendsto_add_atTop_iff_nat 1).mp hs
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology BregmanPPA.Convergence BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n m : ℕ}

theorem original_limit_feasibility
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (pstar : EuclideanSpace ℝ (Fin m))
    (hp : Tendsto p atTop (𝓝 pstar)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x' : EuclideanSpace ℝ (Fin n)) (hx' : Tendsto (x ∘ φ) atTop (𝓝 x')) :
    Tendsto (fun k => A (x k)) atTop (𝓝 b) ∧ A x'=b ∧ x' ∈ X := by
  have hA := original_asymptotic_feasibility A b X f h hh him c hc hcinf x p hrun pstar hp
  have hb := hA.comp hφ.tendsto_atTop
  have ha := A.continuous.continuousAt.tendsto.comp hx'
  have he : A x'=b := tendsto_nhds_unique ha hb
  have hX : ∀ᶠ k in atTop, x k ∈ X := by
    rw [eventually_atTop]
    refine ⟨1,?_⟩
    intro k hk
    cases k with
    | zero => omega
    | succ j => exact (hrun j).1
  exact ⟨hA,he,hP.closed.mem_of_tendsto hx' (hφ.tendsto_atTop.eventually hX)⟩
end BregmanEqMultCodex

end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.Convergence BregmanPPA.EqMult
namespace BregmanEqMultCodex
variable {n m : ℕ}

theorem original_limit_points
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hP : IsEqProgram X f)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h)) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k)
    (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p) (pstar : EuclideanSpace ℝ (Fin m))
    (hp : Tendsto p atTop (𝓝 pstar)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x' : EuclideanSpace ℝ (Fin n)) (hx' : Tendsto (x ∘ φ) atTop (𝓝 x')) :
    Tendsto (fun k => A (x k)) atTop (𝓝 b) ∧ A x'=b ∧
    -(ContinuousLinearMap.adjoint A pstar) ∈ subdiffOp (fX X f) x' ∧
    IsSolution7 A b X f x' := by
  have hf := original_limit_feasibility A b X f hP h hh him c hc hcinf x p hrun pstar hp φ hφ x' hx'
  have hshift := tendsto_add_atTop_nat 1
  have hz : Tendsto (fun k => x (φ (k+1))) atTop (𝓝 x') := hx'.comp hshift
  have hg : Tendsto (fun k => -(ContinuousLinearMap.adjoint A (p (φ (k+1))))) atTop
      (𝓝 (-(ContinuousLinearMap.adjoint A pstar))) :=
    (ContinuousLinearMap.adjoint A).continuous.neg.continuousAt.tendsto.comp
      (hp.comp (hφ.tendsto_atTop.comp hshift))
  have hgraphs (k : ℕ) : IsSubgradient (fX X f) (x (φ (k+1)))
      (-(ContinuousLinearMap.adjoint A (p (φ (k+1))))) := by
    have hpos : 0 < φ (k+1) := lt_of_lt_of_le (Nat.zero_lt_succ k) (hφ.id_le (k+1))
    have he : φ (k+1)-1+1=φ (k+1) := by omega
    simpa only [he,subdiffOp,Set.mem_setOf_eq] using
      original_primal_subgradient A b X f hP h hh him c hc x p hrun (φ (k+1)-1)
  have hs := original_subgradient_graph_limit (fX X f) (original_primal_extension_proper X f hP)
    (original_primal_extension_lsc X f hP) _ _ x' (-(ContinuousLinearMap.adjoint A pstar)) hz hg hgraphs
  refine ⟨hf.1,hf.2.1,hs,hf.2.2,hf.2.1,?_⟩
  intro y hy hAy
  have hb := hs.2 y
  have he : inner ℝ (-(ContinuousLinearMap.adjoint A pstar)) (y-x')=0 := by
    simp only [inner_neg_left,ContinuousLinearMap.adjoint_inner_left,map_sub,
      hAy,hf.2.1,sub_self,inner_zero_right,neg_zero]
  simpa only [fX,indicatorE,if_pos hf.2.2,if_pos hy,add_zero,he,EReal.coe_zero] using hb
end BregmanEqMultCodex

end

set_option autoImplicit false
open Filter Topology InertialFB.IFB ThreeOpSplitting.Convergence BregmanPPA.EqMult
theorem solution {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)) (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hP : IsEqProgram X f) (hd : ∃ p, dualEq A b X f p ≠ ⊥)
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : BregmanPPA.Convergence.IsBregmanFunction Set.univ h)
    (him : Function.Surjective (gradient h))
    (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (hcinf : ∃ ε > 0, ∀ k, ε ≤ c k)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (p : ℕ → EuclideanSpace ℝ (Fin m))
    (hrun : IsEqMultRun A b X f h c x p)
    (pstar : EuclideanSpace ℝ (Fin m)) (hpstar : IsOptimalMultiplier A b X f pstar)
    (hp : Tendsto p atTop (𝓝 pstar))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (x' : EuclideanSpace ℝ (Fin n))
    (hx' : Tendsto (x ∘ φ) atTop (𝓝 x')) :
    Tendsto (fun k => A (x k)) atTop (𝓝 b) ∧ A x' = b ∧
    -(ContinuousLinearMap.adjoint A pstar) ∈ BregmanPPA.Convergence.subdiffOp (fX X f) x' ∧
    IsSolution7 A b X f x' := by
  exact BregmanEqMultCodex.original_limit_points A b X f hP h hh him c hc hcinf x p hrun pstar hp φ hφ x' hx'


#print axioms solution
