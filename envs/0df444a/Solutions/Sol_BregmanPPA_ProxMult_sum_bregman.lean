-- Prove2me | solution 1 for BregmanPPA.ProxMult.sum_bregman
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T00:33:55.057621+00:00
-- url     : https://prove2.me/submissions/31af40a5-8fc1-4031-899e-ca8d485ba51c

import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_ProxMult_Saddle
set_option autoImplicit false
section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex

theorem sum_gradient_pair {n m : ℕ} (hx : E n → ℝ) (hp : E m → ℝ)
    (x : E n) (p : E m) (hdx : DifferentiableAt ℝ hx x)
    (hdp : DifferentiableAt ℝ hp p) :
    gradient (sumFn hx hp) (pair x p) = pair (gradient hx x) (gradient hp p) := by
  let F : PD n m →L[ℝ] E n := WithLp.fstL 2 ℝ (E n) (E m)
  let G : PD n m →L[ℝ] E m := WithLp.sndL 2 ℝ (E n) (E m)
  have hx' := hdx.hasGradientAt.hasFDerivAt.comp (pair x p) F.hasFDerivAt
  have hp' := hdp.hasGradientAt.hasFDerivAt.comp (pair x p) G.hasFDerivAt
  have he := hx'.add hp'
  have hd : HasFDerivAt (sumFn hx hp)
      ((InnerProductSpace.toDual ℝ _) (pair (gradient hx x) (gradient hp p))) (pair x p) := by
    convert he using 1 <;>
      first | rfl | (ext z; simp [sumFn,F,G,pair,WithLp.prod_inner_apply,InnerProductSpace.toDual_apply_apply])
  exact (hasGradientAt_iff_hasFDerivAt.mpr hd).gradient
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex

theorem sum_bregman_pair {n m : ℕ} (hx : E n → ℝ) (hp : E m → ℝ)
    (x y : E n) (p q : E m) (hdy : DifferentiableAt ℝ hx y)
    (hdq : DifferentiableAt ℝ hp q) :
    bregmanD (sumFn hx hp) (pair x p) (pair y q) =
      bregmanD hx x y+bregmanD hp p q := by
  rw [bregmanD,sum_gradient_pair hx hp y q hdy hdq]
  simp only [bregmanD,sumFn,pair,WithLp.prod_inner_apply]
  change hx x+hp p-(hx y+hp q)-
      (inner ℝ (gradient hx y) (x-y)+inner ℝ (gradient hp q) (p-q)) =
    hx x-hx y-inner ℝ (gradient hx y) (x-y)+
      (hp p-hp q-inner ℝ (gradient hp q) (p-q))
  ring
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult ThreeOpSplitting.Convergence
namespace BregmanProxMultCodex

theorem opK_point_in_program {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (z w : PD n m) (hw : w ∈ opK C f g z) :
    z.ofLp.1 ∈ C ∧ z.ofLp.2 ∈ nonnegOrthant m := by
  classical
  have ht := hw.1.1
  change lagr C f g z.ofLp.1 z.ofLp.2 ≠ ⊤ at ht
  have hx : z.ofLp.1 ∈ C := by
    by_contra hn
    exact ht (by simp only [lagr,if_neg hn])
  refine ⟨hx,?_⟩
  have hb := hw.2.1
  change -lagr C f g z.ofLp.1 z.ofLp.2 ≠ ⊤ at hb
  by_contra hn
  exact hb (by simp only [lagr,if_pos hx,if_neg hn,EReal.neg_bot])

theorem opK_dom_subset {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) :
    dom (opK C f g) ⊆ prodZone C (nonnegOrthant m) := by
  rintro z ⟨w,hw⟩
  exact opK_point_in_program C f g z w hw
theorem nonnegOrthant_closed {m : ℕ} : IsClosed (nonnegOrthant m) := by
  have he : nonnegOrthant m = ⋂ i : Fin m, {p : E m | 0 ≤ p i} := by
    ext p
    simp [nonnegOrthant]
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const (by fun_prop)

theorem opK_closure_subset {n m : ℕ} (C : Set (E n)) (f : E n → EReal)
    (g : Fin m → E n → EReal) (Sx : Set (E n)) (Sp : Set (E m))
    (hC : IsClosed C) (hSx : C ⊆ Sx) (hSp : nonnegOrthant m ⊆ Sp) :
    closure (dom (opK C f g)) ⊆ prodZone Sx Sp := by
  have hclosed : IsClosed (prodZone C (nonnegOrthant m)) := by
    change IsClosed ((fun z : PD n m => z.ofLp.1) ⁻¹' C ∩
      (fun z : PD n m => z.ofLp.2) ⁻¹' nonnegOrthant m)
    exact (hC.preimage (by fun_prop)).inter (nonnegOrthant_closed.preimage (by fun_prop))
  have hb := closure_minimal (opK_dom_subset C f g) hclosed
  intro z hz
  have hi := hb hz
  exact ⟨hSx hi.1,hSp hi.2⟩
end BregmanProxMultCodex


end

section
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex
variable {n m : ℕ}

theorem prodZone_closure (Sx : Set (E n)) (Sp : Set (E m)) :
    closure (prodZone Sx Sp) = prodZone (closure Sx) (closure Sp) := by
  let e := WithLp.homeomorphProd 2 (E n) (E m)
  change closure (e ⁻¹' (Sx ×ˢ Sp)) = e ⁻¹' (closure Sx ×ˢ closure Sp)
  rw [← e.preimage_closure,closure_prod_eq]

theorem prodZone_open (Sx : Set (E n)) (Sp : Set (E m))
    (hx : IsOpen Sx) (hp : IsOpen Sp) : IsOpen (prodZone Sx Sp) := by
  change IsOpen ((fun z : PD n m => z.ofLp.1) ⁻¹' Sx ∩
    (fun z : PD n m => z.ofLp.2) ⁻¹' Sp)
  exact (hx.preimage (by fun_prop)).inter (hp.preimage (by fun_prop))

theorem packed_bounded_iff (s : Set (PD n m)) :
    Bornology.IsBounded s ↔
      Bornology.IsBounded ((fun z => z.ofLp.1) '' s) ∧
      Bornology.IsBounded ((fun z => z.ofLp.2) '' s) := by
  change @Bornology.IsBounded _ (Bornology.induced (@WithLp.ofLp 2 (E n × E m))) s ↔ _
  rw [Bornology.isBounded_induced,← Bornology.isBounded_image_fst_and_snd]
  simp only [Set.image_image,Function.comp_def]

theorem prodZone_bounded (Sx : Set (E n)) (Sp : Set (E m))
    (hx : Bornology.IsBounded Sx) (hp : Bornology.IsBounded Sp) :
    Bornology.IsBounded (prodZone Sx Sp) := by
  apply (packed_bounded_iff _).mpr
  constructor
  · apply hx.subset
    rintro _ ⟨z,hz,rfl⟩
    exact hz.1
  · apply hp.subset
    rintro _ ⟨z,hz,rfl⟩
    exact hz.2

theorem sum_contDiffOn (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp) :
    ContDiffOn ℝ 1 (sumFn hx hp) (prodZone Sx Sp) := by
  let F : PD n m →L[ℝ] E n := WithLp.fstL 2 ℝ (E n) (E m)
  let G : PD n m →L[ℝ] E m := WithLp.sndL 2 ℝ (E n) (E m)
  exact (hhx.contDiffOn.comp F.contDiff.contDiffOn (fun z hz => hz.1)).add
    (hhp.contDiffOn.comp G.contDiff.contDiffOn (fun z hz => hz.2))

theorem sum_continuousOn (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp) :
    ContinuousOn (sumFn hx hp) (closure (prodZone Sx Sp)) := by
  rw [prodZone_closure]
  exact (hhx.continuousOn.comp (by fun_prop) (fun z hz => hz.1)).add
    (hhp.continuousOn.comp (by fun_prop) (fun z hz => hz.2))

theorem sum_strictConvexOn (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp) :
    StrictConvexOn ℝ (closure (prodZone Sx Sp)) (sumFn hx hp) := by
  rw [prodZone_closure]
  refine ⟨?_,?_⟩
  · intro x hx' y hy' a b ha hb hab
    exact ⟨hhx.strictConvexOn.1 hx'.1 hy'.1 ha hb hab,
      hhp.strictConvexOn.1 hx'.2 hy'.2 ha hb hab⟩
  · intro x hx' y hy' hne a b ha hb hab
    have hxc := hhx.strictConvexOn.convexOn.2 hx'.1 hy'.1 ha.le hb.le hab
    have hpc := hhp.strictConvexOn.convexOn.2 hx'.2 hy'.2 ha.le hb.le hab
    by_cases he : x.ofLp.1=y.ofLp.1
    · have hn : x.ofLp.2 ≠ y.ofLp.2 := by
        intro hn
        apply hne
        apply WithLp.ofLp_injective
        exact Prod.ext he hn
      have hps := hhp.strictConvexOn.2 hx'.2 hy'.2 hn ha hb hab
      change hx (a • x.ofLp.1+b • y.ofLp.1)+hp (a • x.ofLp.2+b • y.ofLp.2) <
        a*(hx x.ofLp.1+hp x.ofLp.2)+b*(hx y.ofLp.1+hp y.ofLp.2)
      simp only [smul_eq_mul] at hxc hps
      linarith
    · have hxs := hhx.strictConvexOn.2 hx'.1 hy'.1 he ha hb hab
      change hx (a • x.ofLp.1+b • y.ofLp.1)+hp (a • x.ofLp.2+b • y.ofLp.2) <
        a*(hx x.ofLp.1+hp x.ofLp.2)+b*(hx y.ofLp.1+hp y.ofLp.2)
      simp only [smul_eq_mul] at hxs hpc
      linarith

theorem sum_distance (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (x y : PD n m) (hy : y ∈ prodZone Sx Sp) :
    bregmanD (sumFn hx hp) x y =
      bregmanD hx x.ofLp.1 y.ofLp.1+bregmanD hp x.ofLp.2 y.ofLp.2 := by
  have hdx : DifferentiableAt ℝ hx y.ofLp.1 :=
    ((hhx.contDiffOn.differentiableOn (by simp)) _ hy.1).differentiableAt (hhx.isOpen.mem_nhds hy.1)
  have hdp : DifferentiableAt ℝ hp y.ofLp.2 :=
    ((hhp.contDiffOn.differentiableOn (by simp)) _ hy.2).differentiableAt (hhp.isOpen.mem_nhds hy.2)
  exact sum_bregman_pair hx hp x.ofLp.1 y.ofLp.1 x.ofLp.2 y.ofLp.2 hdx hdp
end BregmanProxMultCodex

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
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex
variable {n m : ℕ}

theorem sum_component_bounds (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (x y : PD n m) (hxC : x ∈ closure (prodZone Sx Sp)) (hy : y ∈ prodZone Sx Sp)
    (α : ℝ) (hb : bregmanD (sumFn hx hp) x y ≤ α) :
    bregmanD hx x.ofLp.1 y.ofLp.1 ≤ α ∧ bregmanD hp x.ofLp.2 y.ofLp.2 ≤ α := by
  rw [prodZone_closure] at hxC
  have hn1 := BregmanPPACodex.bregman_nonneg Sx hx hhx hxC.1 hy.1
  have hn2 := BregmanPPACodex.bregman_nonneg Sp hp hhp hxC.2 hy.2
  rw [sum_distance Sx Sp hx hp hhx hhp x y hy] at hb
  constructor <;> linarith

theorem sum_bounded_L1 (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (α : ℝ) (y : PD n m) (hy : y ∈ prodZone Sx Sp) :
    Bornology.IsBounded {x | x ∈ closure (prodZone Sx Sp) ∧ bregmanD (sumFn hx hp) x y ≤ α} := by
  have hb := prodZone_bounded
    {x | x ∈ closure Sx ∧ bregmanD hx x y.ofLp.1 ≤ α}
    {p | p ∈ closure Sp ∧ bregmanD hp p y.ofLp.2 ≤ α}
    (hhx.bounded_L₁ α y.ofLp.1 hy.1) (hhp.bounded_L₁ α y.ofLp.2 hy.2)
  apply hb.subset
  rintro x ⟨hxC,hD⟩
  have hs := sum_component_bounds Sx Sp hx hp hhx hhp x y hxC hy α hD
  rw [prodZone_closure] at hxC
  exact ⟨⟨hxC.1,hs.1⟩,⟨hxC.2,hs.2⟩⟩

theorem sum_bounded_L2 (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (α : ℝ) (x : PD n m) (hxC : x ∈ closure (prodZone Sx Sp)) :
    Bornology.IsBounded {y | y ∈ prodZone Sx Sp ∧ bregmanD (sumFn hx hp) x y ≤ α} := by
  have hC := hxC
  rw [prodZone_closure] at hC
  have hb := prodZone_bounded
    {y | y ∈ Sx ∧ bregmanD hx x.ofLp.1 y ≤ α}
    {q | q ∈ Sp ∧ bregmanD hp x.ofLp.2 q ≤ α}
    (hhx.bounded_L₂ α x.ofLp.1 hC.1) (hhp.bounded_L₂ α x.ofLp.2 hC.2)
  apply hb.subset
  rintro y ⟨hy,hD⟩
  have hs := sum_component_bounds Sx Sp hx hp hhx hhp x y hxC hy α hD
  exact ⟨⟨hy.1,hs.1⟩,⟨hy.2,hs.2⟩⟩

theorem sum_tendsto_zero (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (y : ℕ → PD n m) (y' : PD n m) (hy : ∀ k, y k ∈ prodZone Sx Sp)
    (ht : Tendsto y atTop (𝓝 y')) :
    Tendsto (fun k => bregmanD (sumFn hx hp) y' (y k)) atTop (𝓝 0) := by
  have hxT := (show Continuous (fun z : PD n m => z.ofLp.1) by fun_prop).tendsto y' |>.comp ht
  have hpT := (show Continuous (fun z : PD n m => z.ofLp.2) by fun_prop).tendsto y' |>.comp ht
  have h1 := hhx.tendsto_zero (fun k => (y k).ofLp.1) y'.ofLp.1 (fun k => (hy k).1) hxT
  have h2 := hhp.tendsto_zero (fun k => (y k).ofLp.2) y'.ofLp.2 (fun k => (hy k).2) hpT
  have he : (fun k => bregmanD (sumFn hx hp) y' (y k)) =
      (fun k => bregmanD hx y'.ofLp.1 (y k).ofLp.1+bregmanD hp y'.ofLp.2 (y k).ofLp.2) := by
    funext k
    exact sum_distance Sx Sp hx hp hhx hhp y' (y k) (hy k)
  rw [he]
  simpa using h1.add h2

theorem sum_tendsto_of_zero (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp)
    (x y : ℕ → PD n m) (y' : PD n m)
    (hxC : ∀ k, x k ∈ closure (prodZone Sx Sp)) (hy : ∀ k, y k ∈ prodZone Sx Sp)
    (hyT : Tendsto y atTop (𝓝 y')) (hyC : y' ∈ closure (prodZone Sx Sp))
    (hB : Bornology.IsBounded (Set.range x))
    (hD : Tendsto (fun k => bregmanD (sumFn hx hp) (x k) (y k)) atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 y') := by
  have hC (k : ℕ) : (x k).ofLp.1 ∈ closure Sx ∧ (x k).ofLp.2 ∈ closure Sp := by
    have hi := hxC k
    rw [prodZone_closure] at hi
    exact hi
  have hnn1 (k : ℕ) : 0 ≤ bregmanD hx (x k).ofLp.1 (y k).ofLp.1 :=
    BregmanPPACodex.bregman_nonneg Sx hx hhx (hC k).1 (hy k).1
  have hnn2 (k : ℕ) : 0 ≤ bregmanD hp (x k).ofLp.2 (y k).ofLp.2 :=
    BregmanPPACodex.bregman_nonneg Sp hp hhp (hC k).2 (hy k).2
  have hd1 : Tendsto (fun k => bregmanD hx (x k).ofLp.1 (y k).ofLp.1) atTop (𝓝 0) := by
    apply squeeze_zero hnn1 _ hD
    intro k
    rw [sum_distance Sx Sp hx hp hhx hhp (x k) (y k) (hy k)]
    linarith [hnn2 k]
  have hd2 : Tendsto (fun k => bregmanD hp (x k).ofLp.2 (y k).ofLp.2) atTop (𝓝 0) := by
    apply squeeze_zero hnn2 _ hD
    intro k
    rw [sum_distance Sx Sp hx hp hhx hhp (x k) (y k) (hy k)]
    linarith [hnn1 k]
  have hyT1 := (show Continuous (fun z : PD n m => z.ofLp.1) by fun_prop).tendsto y' |>.comp hyT
  have hyT2 := (show Continuous (fun z : PD n m => z.ofLp.2) by fun_prop).tendsto y' |>.comp hyT
  have hb := (packed_bounded_iff (Set.range x)).mp hB
  have hb1 : Bornology.IsBounded (Set.range (fun k => (x k).ofLp.1)) := by
    apply hb.1.subset
    rintro _ ⟨k,rfl⟩
    exact ⟨x k,⟨k,rfl⟩,rfl⟩
  have hb2 : Bornology.IsBounded (Set.range (fun k => (x k).ofLp.2)) := by
    apply hb.2.subset
    rintro _ ⟨k,rfl⟩
    exact ⟨x k,⟨k,rfl⟩,rfl⟩
  rw [prodZone_closure] at hyC
  have ht1 := hhx.tendsto_of_zero (fun k => (x k).ofLp.1) (fun k => (y k).ofLp.1) y'.ofLp.1
    (fun k => (hC k).1) (fun k => (hy k).1) hyT1 hyC.1 hb1 hd1
  have ht2 := hhp.tendsto_of_zero (fun k => (x k).ofLp.2) (fun k => (y k).ofLp.2) y'.ofLp.2
    (fun k => (hC k).2) (fun k => (hy k).2) hyT2 hyC.2 hb2 hd2
  exact (WithLp.prod_continuous_toLp 2 (E n) (E m)).tendsto (y'.ofLp) |>.comp (ht1.prodMk_nhds ht2)
end BregmanProxMultCodex

end

section
set_option autoImplicit false
open BregmanPPA.IneqMult BregmanPPA.ProxMult BregmanPPA.Convergence
namespace BregmanProxMultCodex

theorem product_bregman {n m : ℕ} (Sx : Set (E n)) (Sp : Set (E m))
    (hx : E n → ℝ) (hp : E m → ℝ)
    (hhx : IsBregmanFunction Sx hx) (hhp : IsBregmanFunction Sp hp) :
    IsBregmanFunction (prodZone Sx Sp) (sumFn hx hp) where
  isOpen := prodZone_open Sx Sp hhx.isOpen hhp.isOpen
  contDiffOn := sum_contDiffOn Sx Sp hx hp hhx hhp
  strictConvexOn := sum_strictConvexOn Sx Sp hx hp hhx hhp
  continuousOn := sum_continuousOn Sx Sp hx hp hhx hhp
  bounded_L₁ := sum_bounded_L1 Sx Sp hx hp hhx hhp
  bounded_L₂ := sum_bounded_L2 Sx Sp hx hp hhx hhp
  tendsto_zero := sum_tendsto_zero Sx Sp hx hp hhx hhp
  tendsto_of_zero := sum_tendsto_of_zero Sx Sp hx hp hhx hhp
end BregmanProxMultCodex

end

set_option autoImplicit false
open BregmanPPA.ProxMult ThreeOpSplitting.Convergence
theorem solution {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp) :
    BregmanPPA.Convergence.IsBregmanFunction (prodZone Sx Sp) (sumFn hx hp) ∧
    closure (dom (opK C f g)) ⊆ prodZone Sx Sp :=
  ⟨BregmanProxMultCodex.product_bregman Sx Sp hx hp hhx hhp,
    BregmanProxMultCodex.opK_closure_subset C f g Sx Sp hP.closed hSx hSp⟩

#print axioms solution
