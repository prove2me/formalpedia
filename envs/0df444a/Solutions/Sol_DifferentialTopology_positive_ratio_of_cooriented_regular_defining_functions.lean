-- Prove2me | solution 1 for DifferentialTopology.positive_ratio_of_cooriented_regular_defining_functions
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T20:25:21.568074+00:00
-- url     : https://prove2.me/submissions/7bb5f871-cb68-41f4-a45d-19b683416088

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Theorems.Thm_FiniteEnergyPlane_hadamard_integral_fderiv

namespace SmoothDivision
open Set Filter Function Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma smooth_local_extension
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (p : E) (hp : p ∈ U) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 p] f := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let χ : ContDiffBump p :=
    { rIn := r/4
      rOut := r/2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hs : tsupport χ ⊆ U := by
    rw [χ.tsupport_eq]
    intro x hx
    apply hball
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith : r/2 < r)
  let g : E → F := fun x => χ x • f x
  refine ⟨g,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport χ
    · exact χ.contDiffAt.smul ((hf x (hs hx)).contDiffAt (hU.mem_nhds (hs hx)))
    · have he : g =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
        simp [g,hy]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · filter_upwards [χ.eventuallyEq_one] with x hx
    simp [g,hx]

lemma smooth_local_inverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : E → E) (hf : ContDiff ℝ ∞ f) (p : E)
    (hD : IsUnit (fderiv ℝ f p)) :
    ∃ g : E → E, ContDiff ℝ ∞ g ∧ g (f p) = p ∧
      (∀ᶠ x in 𝓝 p, g (f x) = x) ∧ (∀ᶠ y in 𝓝 (f p), f (g y) = y) := by
  let A : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit hD.unit
  have hA : (A : E →L[ℝ] E) = fderiv ℝ f p := hD.unit_spec
  have hd : HasFDerivAt f (A : E →L[ℝ] E) p := by
    rw [hA]
    exact (hf.differentiable (by simp) p).hasFDerivAt
  let e := hf.contDiffAt.toOpenPartialHomeomorph f hd (by simp)
  have hcoe : (e : E → E) = f := rfl
  have hp : p ∈ e.source := hf.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by simp)
  have hfp : f p ∈ e.target := hf.contDiffAt.image_mem_toOpenPartialHomeomorph_target hd (by simp)
  let O : Set E := {x | IsUnit (fderiv ℝ f x)}
  have hO : IsOpen O := Units.isOpen.preimage (hf.continuous_fderiv (by simp))
  let W := e.target ∩ e.symm ⁻¹' O
  have hW : IsOpen W := e.continuousOn_symm.isOpen_inter_preimage e.open_target hO
  have hWp : f p ∈ W := by
    refine ⟨hfp,?_⟩
    change IsUnit (fderiv ℝ f (e.symm (f p)))
    rw [← hcoe,e.left_inv hp]
    exact hD
  have hInv : ContDiffOn ℝ ∞ e.symm W := by
    intro y hy
    have hunit : IsUnit (fderiv ℝ f (e.symm y)) := hy.2
    let B : E ≃L[ℝ] E := ContinuousLinearEquiv.ofUnit hunit.unit
    have hB : (B : E →L[ℝ] E) = fderiv ℝ f (e.symm y) := hunit.unit_spec
    have hdy : HasFDerivAt e (B : E →L[ℝ] E) (e.symm y) := by
      rw [hcoe,hB]
      exact (hf.differentiable (by simp) _).hasFDerivAt
    exact (e.contDiffAt_symm hy.1 hdy (by rw [hcoe]; exact hf.contDiffAt)).contDiffWithinAt
  obtain ⟨g,hg,he⟩ := smooth_local_extension e.symm W hW hInv (f p) hWp
  have hgp : g (f p) = p := by
    rw [he.eq_of_nhds,← hcoe,e.left_inv hp]
  refine ⟨g,hg,hgp,?_,?_⟩
  · filter_upwards [hf.continuous.continuousAt.eventually he,e.open_source.mem_nhds hp] with x hx hs
    rw [hx,← hcoe,e.left_inv hs]
  · filter_upwards [he,e.open_target.mem_nhds hfp] with y hy ht
    rw [hy,← hcoe,e.right_inv ht]

end
end SmoothDivision


namespace SmoothDivision
open Set Filter Function Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev Plane := ℝ × ℝ

lemma local_division_from_chart (u v : Plane → ℝ) (hu : ContDiff ℝ ∞ u)
    (f : Plane → Plane) (hf : ContDiff ℝ ∞ f) (hsnd : ∀ x, (f x).2 = v x)
    (p : Plane) (hp : v p = 0) (hD : IsUnit (fderiv ℝ f p))
    (hzero : ∀ x, v x = 0 → u x = 0) :
    ∃ a : Plane → ℝ, ContDiff ℝ ∞ a ∧ ∀ᶠ x in 𝓝 p, u x = a x*v x := by
  obtain ⟨g,hg,hgp,hleft,hright⟩ := smooth_local_inverse f hf p hD
  let F : ℝ × ℝ → ℝ := fun q => u (g q)
  have hF : ContDiff ℝ ∞ F := hu.comp hg
  let G : Plane → (ℝ →L[ℝ] ℝ) :=
    fun q => ∫ θ in (0:ℝ)..1, fderiv ℝ (fun z => F (q.1,z)) (θ • q.2)
  obtain ⟨hG,hidentity⟩ := FiniteEnergyPlane.hadamard_integral_fderiv F hF
  change ContDiff ℝ ∞ G at hG
  have ht : Tendsto (fun q : Plane => (q.1,(0:ℝ))) (𝓝 (f p)) (𝓝 (f p)) := by
    have hc : Continuous (fun q : Plane => (q.1,(0:ℝ))) := continuous_fst.prodMk continuous_const
    have hct : ContinuousAt (fun q : Plane => (q.1,(0:ℝ))) (f p) := hc.continuousAt
    have he : ((f p).1,(0:ℝ)) = f p := Prod.ext rfl (by rw [hsnd,hp])
    change Tendsto _ _ (𝓝 ((f p).1,(0:ℝ))) at hct
    rw [he] at hct
    exact hct
  have hzeroF : ∀ᶠ q : Plane in 𝓝 (f p), F (q.1,0) = 0 := by
    filter_upwards [ht.eventually hright] with q hq
    apply hzero
    have he := congrArg Prod.snd hq
    simpa only [hsnd] using he
  let a : Plane → ℝ := fun x => G (f x) 1
  have ha : ContDiff ℝ ∞ a := (hG.comp hf).clm_apply contDiff_const
  refine ⟨a,ha,?_⟩
  filter_upwards [hleft,hf.continuous.continuousAt.eventually hzeroF] with x hx hz
  have hid := hidentity (f x)
  change F (f x) = F ((f x).1,0)+G (f x) (f x).2 at hid
  have he : F (f x) = u x := by dsimp only [F]; rw [hx]
  rw [he,hz,zero_add,hsnd] at hid
  rw [hid]
  change G (f x) (v x) = G (f x) 1*v x
  calc
    G (f x) (v x) = G (f x) ((v x) • (1:ℝ)) := by simp
    _ = (v x) • G (f x) 1 := map_smul _ _ _
    _ = G (f x) 1*v x := by simp [mul_comm]

lemma covector_expansion (D : Plane →L[ℝ] ℝ) (x : Plane) :
    D x = D (1,0)*x.1+D (0,1)*x.2 := by
  have he : x = x.1 • (1,0)+x.2 • (0,1) := by ext <;> simp
  calc
    D x = D (x.1 • (1,0)+x.2 • (0,1)) := congrArg D he
    _ = D (1,0)*x.1+D (0,1)*x.2 := by
      rw [map_add,map_smul,map_smul]
      simp [mul_comm]

lemma exists_complementary_covector (D : Plane →L[ℝ] ℝ) (hD : D ≠ 0) :
    ∃ L : Plane →L[ℝ] ℝ, Bijective (L.prod D) := by
  let a := D (1,0)
  let b := D (0,1)
  let S := a^2+b^2
  have hS : 0 < S := by
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hD
      apply ContinuousLinearMap.ext
      intro x
      change D x = 0
      rw [covector_expansion]
      simp only [show D (1,0) = 0 from hn.1,show D (0,1) = 0 from hn.2,zero_mul,add_zero]
    rcases hab with ha|hb
    · dsimp [S]
      nlinarith [sq_pos_of_ne_zero ha,sq_nonneg b]
    · dsimp [S]
      nlinarith [sq_pos_of_ne_zero hb,sq_nonneg a]
  let L : Plane →L[ℝ] ℝ := b • ContinuousLinearMap.fst ℝ ℝ ℝ-a • ContinuousLinearMap.snd ℝ ℝ ℝ
  let R : Plane → Plane := fun q => ((b*q.1+a*q.2)/S,(-a*q.1+b*q.2)/S)
  have heL : ∀ x, L x = b*x.1-a*x.2 := by intro x; simp [L]
  have heD : ∀ x, D x = a*x.1+b*x.2 := by intro x; exact covector_expansion D x
  have hleft : LeftInverse R (L.prod D) := by
    intro x
    ext
    · change (b*L x+a*D x)/S = x.1
      rw [heL,heD]
      dsimp [S]
      field_simp [show a^2+b^2 ≠ 0 from hS.ne']
      <;> ring
    · change (-a*L x+b*D x)/S = x.2
      rw [heL,heD]
      dsimp [S]
      field_simp [show a^2+b^2 ≠ 0 from hS.ne']
      <;> ring
  have hright : RightInverse R (L.prod D) := by
    intro q
    ext
    · change L (R q) = q.1
      rw [heL]
      dsimp [R]
      field_simp [hS.ne']
      <;> ring
    · change D (R q) = q.2
      rw [heD]
      dsimp [R]
      field_simp [hS.ne']
      <;> ring
  exact ⟨L,hleft.injective,hright.surjective⟩

lemma local_division (u v : Plane → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (p : Plane) (hp : v p = 0) (hD : fderiv ℝ v p ≠ 0)
    (hzero : ∀ x, v x = 0 → u x = 0) :
    ∃ a : Plane → ℝ, ContDiff ℝ ∞ a ∧ ∀ᶠ x in 𝓝 p, u x = a x*v x := by
  obtain ⟨L,hL⟩ := exists_complementary_covector (fderiv ℝ v p) hD
  let f : Plane → Plane := fun x => (L x,v x)
  have hf : ContDiff ℝ ∞ f := L.contDiff.prodMk hv
  have hd : fderiv ℝ f p = L.prod (fderiv ℝ v p) :=
    (L.hasFDerivAt.prodMk ((hv.differentiable (by simp) p).hasFDerivAt)).fderiv
  have huD : IsUnit (fderiv ℝ f p) := by
    rw [hd,ContinuousLinearMap.isUnit_iff_bijective]
    exact hL
  exact local_division_from_chart u v hu f hf (fun _ => rfl) p hp huD hzero

end
end SmoothDivision


namespace SmoothDivision
open Set Filter Function Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

lemma exists_unit_direction (D : Plane →L[ℝ] ℝ) (hD : D ≠ 0) : ∃ w, D w = 1 := by
  have he : ∃ x, D x ≠ 0 := by
    by_contra hn
    push_neg at hn
    apply hD
    exact ContinuousLinearMap.ext hn
  obtain ⟨x,hx⟩ := he
  refine ⟨(D x)⁻¹ • x,?_⟩
  rw [map_smul]
  simp [hx]

lemma factor_derivative_on_zero (u v a : Plane → ℝ)
    (hv : ContDiff ℝ ∞ v) (ha : ContDiff ℝ ∞ a) (p : Plane) (hp : v p = 0)
    (heq : u =ᶠ[𝓝 p] (fun x => a x*v x)) :
    fderiv ℝ u p = a p • fderiv ℝ v p := by
  rw [heq.fderiv_eq,fderiv_fun_mul (ha.differentiable (by simp) p) (hv.differentiable (by simp) p)]
  simp [hp]

lemma exists_smooth_factor (u v : Plane → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hreg : ∀ x, v x = 0 → fderiv ℝ v x ≠ 0) (hzero : ∀ x, v x = 0 → u x = 0) :
    ∃ a : Plane → ℝ, ContDiff ℝ ∞ a ∧ ∀ x, u x = a x*v x := by
  have hw : ∀ x, ∃ w : Plane, v x = 0 → fderiv ℝ v x w = 1 := by
    intro x
    by_cases hx : v x = 0
    · obtain ⟨w,hw⟩ := exists_unit_direction (fderiv ℝ v x) (hreg x hx)
      exact ⟨w,fun _ => hw⟩
    · exact ⟨0,fun h => (hx h).elim⟩
  choose w hw using hw
  let a : Plane → ℝ := fun x => if v x = 0 then fderiv ℝ u x (w x) else u x/v x
  have ha : ContDiff ℝ ∞ a := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : v p = 0
    · obtain ⟨b,hb,hfactor⟩ := local_division u v hu hv p hp (hreg p hp) hzero
      obtain ⟨U,hU,hUopen,hpU⟩ := mem_nhds_iff.mp hfactor
      have hevent : a =ᶠ[𝓝 p] b := by
        filter_upwards [hUopen.mem_nhds hpU] with x hx
        by_cases hz : v x = 0
        · have heq : u =ᶠ[𝓝 x] (fun y => b y*v y) :=
            Filter.mem_of_superset (hUopen.mem_nhds hx) hU
          have hd := factor_derivative_on_zero u v b hv hb x hz heq
          simp [a,hz,hd,hw x hz]
        · have heq : u x = b x*v x := hU hx
          simp [a,hz,heq]
      exact hb.contDiffAt.congr_of_eventuallyEq hevent
    · have hevent : a =ᶠ[𝓝 p] (fun x => u x/v x) := by
        filter_upwards [hv.continuous.continuousAt.eventually_ne hp] with x hx
        simp [a,hx]
      exact (hu.contDiffAt.div hv.contDiffAt hp).congr_of_eventuallyEq hevent
  refine ⟨a,ha,?_⟩
  intro x
  by_cases hx : v x = 0
  · simp [hx,hzero x hx]
  · simp [a,hx]

lemma smooth_factor_unique (u v a b : Plane → ℝ)
    (hv : ContDiff ℝ ∞ v) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hreg : ∀ x, v x = 0 → fderiv ℝ v x ≠ 0)
    (hea : ∀ x, u x = a x*v x) (heb : ∀ x, u x = b x*v x) : a = b := by
  funext x
  by_cases hx : v x = 0
  · obtain ⟨w,hw⟩ := exists_unit_direction (fderiv ℝ v x) (hreg x hx)
    have hda := factor_derivative_on_zero u v a hv ha x hx (Filter.Eventually.of_forall hea)
    have hdb := factor_derivative_on_zero u v b hv hb x hx (Filter.Eventually.of_forall heb)
    have he := congrArg (fun D : Plane →L[ℝ] ℝ => D w) (hda.symm.trans hdb)
    simpa [hw] using he
  · exact mul_right_cancel₀ hx ((hea x).symm.trans (heb x))

theorem positive_defining_function_ratio (u v : Plane → ℝ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hregu : ∀ x, u x = 0 → fderiv ℝ u x ≠ 0)
    (hregv : ∀ x, v x = 0 → fderiv ℝ v x ≠ 0)
    (hzero : ∀ x, u x = 0 ↔ v x = 0)
    (hsign : ∀ x, v x ≠ 0 → 0 < u x*v x) :
    ∃! a : Plane → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 < a x) ∧ ∀ x, u x = a x*v x := by
  obtain ⟨a,ha,hfactor⟩ := exists_smooth_factor u v hu hv hregv (fun x hx => (hzero x).mpr hx)
  have hposoff : ∀ x, v x ≠ 0 → 0 < a x := by
    intro x hx
    have hp := hsign x hx
    rw [hfactor x,mul_assoc] at hp
    have hvv : 0 < v x*v x := mul_self_pos.mpr hx
    exact (mul_pos_iff_of_pos_right hvv).mp hp
  have hpos : ∀ x, 0 < a x := by
    intro p
    by_cases hp : v p = 0
    · have hd := factor_derivative_on_zero u v a hv ha p hp (Filter.Eventually.of_forall hfactor)
      have hne : a p ≠ 0 := by
        intro hz
        apply hregu p ((hzero p).mpr hp)
        rw [hd,hz,zero_smul]
      have hnonneg : 0 ≤ a p := by
        by_contra hn
        have hneg : a p < 0 := lt_of_not_ge hn
        have hnear : ∀ᶠ x in 𝓝 p, a x < 0 := ha.continuous.continuousAt.eventually (Iio_mem_nhds hneg)
        have hzeroNear : v =ᶠ[𝓝 p] (fun _ => 0) := by
          filter_upwards [hnear] with x hx
          by_contra hvx
          exact (not_lt_of_ge (hposoff x hvx).le) hx
        apply hregv p hp
        simpa using hzeroNear.fderiv_eq
      exact lt_of_le_of_ne hnonneg (Ne.symm hne)
    · exact hposoff p hp
  refine ⟨a,⟨ha,hpos,hfactor⟩,?_⟩
  intro b hb
  exact smooth_factor_unique u v b a hv hb.1 ha hregv hb.2.2 hfactor

end
end SmoothDivision


open scoped ContDiff

theorem solution
    (u v : (ℝ × ℝ) → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hregu : ∀ x, u x = 0 → fderiv ℝ u x ≠ 0)
    (hregv : ∀ x, v x = 0 → fderiv ℝ v x ≠ 0)
    (hzero : ∀ x, u x = 0 ↔ v x = 0)
    (hsign : ∀ x, v x ≠ 0 → 0 < u x*v x) :
    ∃! a : (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 < a x) ∧ ∀ x, u x = a x*v x := by
  exact SmoothDivision.positive_defining_function_ratio u v hu hv hregu hregv hzero hsign
