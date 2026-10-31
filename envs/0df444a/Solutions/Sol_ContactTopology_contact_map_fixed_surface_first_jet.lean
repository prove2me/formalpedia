-- Prove2me | solution 1 for ContactTopology.contact_map_fixed_surface_first_jet
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T23:01:28.418422+00:00
-- url     : https://prove2.me/submissions/4a346fd9-04c0-4bf1-adc2-107ba2a72f5d

import Theorems.Thm_ContactCalculus_exterior_pairing_pullback
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring


namespace ContactTopology.FixedSurface
open Set Function Filter Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section


abbrev V := Fin 3 → ℝ

def dot (a v : V) : ℝ := a 0*v 0+a 1*v 1+a 2*v 2

def cross (a b : V) : V :=
  ![a 1*b 2-a 2*b 1,a 2*b 0-a 0*b 2,a 0*b 1-a 1*b 0]

def covector : V →L[ℝ] (V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ)+
  (ContinuousLinearMap.proj 1 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 1 : V →L[ℝ] ℝ)+
  (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj 2 : V →L[ℝ] ℝ)

lemma covector_apply (a v : V) : covector a v = dot a v := by
  simp [covector,dot]

lemma vector_expansion (v : V) :
    v = v 0 • Pi.single 0 1+v 1 • Pi.single 1 1+v 2 • Pi.single 2 1 := by
  ext i
  fin_cases i <;> simp

def curlLinear (D : V →L[ℝ] V) : V :=
  ![D (Pi.single 1 1) 2-D (Pi.single 2 1) 1,
    D (Pi.single 2 1) 0-D (Pi.single 0 1) 2,
    D (Pi.single 0 1) 1-D (Pi.single 1 1) 0]

lemma exterior_cross (D : V →L[ℝ] V) (u v : V) :
    dot (D u) v-dot (D v) u = dot (curlLinear D) (cross u v) := by
  have hu : D u = u 0 • D (Pi.single 0 1)+u 1 • D (Pi.single 1 1)+u 2 • D (Pi.single 2 1) := by
    conv_lhs => rw [vector_expansion u]
    simp only [map_add,map_smul]
  have hv : D v = v 0 • D (Pi.single 0 1)+v 1 • D (Pi.single 1 1)+v 2 • D (Pi.single 2 1) := by
    conv_lhs => rw [vector_expansion v]
    simp only [map_add,map_smul]
  rw [hu,hv]
  simp [dot,curlLinear,cross]
  ring



def center : V →L[ℝ] V := ContinuousLinearMap.pi
  ![(ContinuousLinearMap.proj 0 : V →L[ℝ] ℝ),ContinuousLinearMap.proj 1,0]
@[simp] lemma center_apply (y : V) : center y = ![y 0,y 1,0] := by ext i; fin_cases i <;> simp [center]
@[simp] lemma center_two (y : V) : center y 2 = 0 := by simp [center]



lemma weighted_covector_fderiv (L : V → ℝ) (a : V → V) (y u v : V)
    (hL : DifferentiableAt ℝ L y) (ha : DifferentiableAt ℝ a y) :
    fderiv ℝ (fun z => L z • covector (a z)) y u v =
      fderiv ℝ L y u*dot (a y) v+L y*dot (fderiv ℝ a y u) v := by
  have hd := hL.hasFDerivAt.smul (covector.hasFDerivAt.comp y ha.hasFDerivAt)
  change HasFDerivAt (fun z => L z • covector (a z)) _ y at hd
  rw [hd.fderiv]
  simp [covector_apply]
  ring

lemma contact_exterior (a F : V → V) (L : V → ℝ) (O : Set V) (hO : IsOpen O)
    (ha : ContDiff ℝ ∞ a) (hF : ContDiffOn ℝ ∞ F O) (hL : ContDiffOn ℝ ∞ L O)
    (hpb : ∀ y ∈ O, ∀ v, covector (a (F y)) (fderiv ℝ F y v)=L y*covector (a y) v)
    (y : V) (hy : y ∈ O) (u v : V) :
    dot (curlLinear (fderiv ℝ a (F y))) (cross (fderiv ℝ F y u) (fderiv ℝ F y v)) =
      fderiv ℝ L y u*dot (a y) v-fderiv ℝ L y v*dot (a y) u+
        L y*dot (curlLinear (fderiv ℝ a y)) (cross u v) := by
  have hFa := hF.contDiffAt (hO.mem_nhds hy)
  have hLa := hL.contDiffAt (hO.mem_nhds hy)
  have heq : (fun z => (covector (a (F z))).comp (fderiv ℝ F z)) =ᶠ[𝓝 y]
      (fun z => L z • covector (a z)) := by
    filter_upwards [hO.mem_nhds hy] with z hz
    ext w
    exact hpb z hz w
  have hn := ContactCalculus.exterior_pairing_pullback (fun z => covector (a z)) F y u v
    (covector.differentiableAt.comp _ (ha.differentiable (by simp) _))
    (hFa.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hD (z w q : V) : fderiv ℝ (fun z => covector (a z)) z w q=dot (fderiv ℝ a z w) q := by
    have hd := covector.hasFDerivAt.comp z (ha.differentiable (by simp) z).hasFDerivAt
    change HasFDerivAt (fun z => covector (a z)) _ z at hd
    rw [hd.fderiv]
    exact covector_apply _ _
  rw [heq.fderiv_eq,weighted_covector_fderiv L a y u v (hLa.differentiableAt (by simp))
      (ha.differentiable (by simp) y),
    weighted_covector_fderiv L a y v u (hLa.differentiableAt (by simp))
      (ha.differentiable (by simp) y),hD,hD] at hn
  rw [← exterior_cross,← exterior_cross]
  linarith [hn]

lemma fixed_plane_derivative (F : V → V) (O : Set V) (hO : IsOpen O)
    (hF : ContDiffOn ℝ ∞ F O) (hfix : ∀ z ∈ O, z 2=0 → F z=z)
    (y : V) (hy : y ∈ O) (hy0 : y 2=0) :
    F y=y ∧ fderiv ℝ F y (Pi.single 0 1)=Pi.single 0 1 ∧
      fderiv ℝ F y (Pi.single 1 1)=Pi.single 1 1 := by
  have hc : center y=y := by ext i; fin_cases i <;> simp [center,hy0]
  have he : F ∘ center =ᶠ[𝓝 y] (center : V → V) := by
    have hcO : center y ∈ O := by rw [hc]; exact hy
    have hm : center ⁻¹' O ∈ 𝓝 y := center.continuous.continuousAt.preimage_mem_nhds
      (hO.mem_nhds hcO)
    filter_upwards [hm] with z hz
    exact hfix (center z) hz (center_two z)
  have hd : fderiv ℝ (F ∘ center) y=fderiv ℝ (center : V → V) y := he.fderiv_eq
  rw [fderiv_comp y (by rw [hc]; exact (hF.contDiffAt (hO.mem_nhds hy)).differentiableAt (by simp))
    center.differentiableAt,ContinuousLinearMap.fderiv] at hd
  rw [hc] at hd
  refine ⟨hfix y hy hy0,?_,?_⟩
  · have hh := congrArg (fun L : V →L[ℝ] V => L (Pi.single 0 1)) hd
    have he0 : center (Pi.single 0 1)=Pi.single 0 1 := by ext i; fin_cases i <;> simp [center]
    simpa only [ContinuousLinearMap.comp_apply,he0] using hh
  · have hh := congrArg (fun L : V →L[ℝ] V => L (Pi.single 1 1)) hd
    have he1 : center (Pi.single 1 1)=Pi.single 1 1 := by ext i; fin_cases i <;> simp [center]
    simpa only [ContinuousLinearMap.comp_apply,he1] using hh


theorem fixed_surface_first_jet (a F : V → V) (L : V → ℝ) (O : Set V) (hO : IsOpen O)
    (ha : ContDiff ℝ ∞ a) (hF : ContDiffOn ℝ ∞ F O) (hL : ContDiffOn ℝ ∞ L O)
    (hpb : ∀ y ∈ O, ∀ v, covector (a (F y)) (fderiv ℝ F y v)=L y*covector (a y) v)
    (hfix : ∀ z ∈ O, z 2=0 → F z=z)
    (y : V) (hy : y ∈ O) (hy0 : y 2=0)
    (hQ : dot (a y) (curlLinear (fderiv ℝ a y)) ≠ 0) :
    L y=1 ∧ fderiv ℝ F y (Pi.single 2 1) 2=1 := by
  obtain ⟨hFy,h0,h1⟩ := fixed_plane_derivative F O hO hF hfix y hy hy0
  have hα0 : a y 0=L y*a y 0 := by simpa [hFy,h0,covector_apply,dot] using hpb y hy (Pi.single 0 1)
  have hα1 : a y 1=L y*a y 1 := by simpa [hFy,h1,covector_apply,dot] using hpb y hy (Pi.single 1 1)
  have hE01 := contact_exterior a F L O hO ha hF hL hpb y hy (Pi.single 0 1) (Pi.single 1 1)
  rw [hFy,h0,h1] at hE01
  have hOne : L y=1 := by
    by_cases ha0 : a y 0=0
    · by_cases ha1 : a y 1=0
      · have hc : curlLinear (fderiv ℝ a y) 2 ≠ 0 := by
          intro hz
          apply hQ
          simp [dot,ha0,ha1,hz]
        have he : (L y-1)*curlLinear (fderiv ℝ a y) 2=0 := by
          simp [dot,cross,ha0,ha1] at hE01
          linarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hc)
      · have he : (L y-1)*a y 1=0 := by linarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right ha1)
    · have he : (L y-1)*a y 0=0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right ha0)
  refine ⟨hOne,?_⟩
  let c := curlLinear (fderiv ℝ a y)
  let v := fderiv ℝ F y (Pi.single 2 1)
  have hA : dot (a y) v=a y 2 := by simpa [hFy,hOne,covector_apply,dot,v] using hpb y hy (Pi.single 2 1)
  have hE12 := contact_exterior a F L O hO ha hF hL hpb y hy (Pi.single 1 1) (Pi.single 2 1)
  have hE20 := contact_exterior a F L O hO ha hF hL hpb y hy (Pi.single 2 1) (Pi.single 0 1)
  rw [hFy,h1,hOne] at hE12
  rw [hFy,h0,hOne] at hE20
  rw [hOne] at hE01
  change dot c (cross (Pi.single 1 1) v)=_ at hE12
  change dot c (cross v (Pi.single 0 1))=_ at hE20
  change dot c (cross (Pi.single 0 1) (Pi.single 1 1))=_ at hE01
  change dot c _ = _ - _ + 1*dot c _ at hE12 hE20 hE01
  have he : dot (a y) c*(v 2-1)=0 := by
    simp only [dot,cross,Pi.single_apply,Fin.reduceEq,ite_true,ite_false,mul_one,mul_zero,
      zero_mul,zero_sub,sub_zero,zero_add,add_zero,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,one_mul] at hE12 hE20 hE01 hA ⊢
    linear_combination (a y 0)*hE12+(a y 1)*hE20+(a y 2)*hE01+(c 2)*hA
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hQ)



end
end ContactTopology.FixedSurface


open Set
open scoped ContDiff


theorem solution
    (a F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (L : (Fin 3 → ℝ) → ℝ)
    (O : Set (Fin 3 → ℝ)) (hO : IsOpen O)
    (ha : ContDiff ℝ ∞ a) (hF : ContDiffOn ℝ ∞ F O) (hL : ContDiffOn ℝ ∞ L O)
    (hfix : ∀ z ∈ O, z 2=0 → F z=z)
    (y : Fin 3 → ℝ) (hy : y ∈ O) (hy0 : y 2=0) :
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun p v => p 0*v 0+p 1*v 1+p 2*v 2
    let c : (Fin 3 → ℝ) :=
      ![fderiv ℝ a y (Pi.single 1 1) 2-fderiv ℝ a y (Pi.single 2 1) 1,
        fderiv ℝ a y (Pi.single 2 1) 0-fderiv ℝ a y (Pi.single 0 1) 2,
        fderiv ℝ a y (Pi.single 0 1) 1-fderiv ℝ a y (Pi.single 1 1) 0]
    (∀ z ∈ O, ∀ v, B (a (F z)) (fderiv ℝ F z v)=L z*B (a z) v) →
    B (a y) c ≠ 0 →
      L y=1 ∧ fderiv ℝ F y (Pi.single 0 1)=Pi.single 0 1 ∧
      fderiv ℝ F y (Pi.single 1 1)=Pi.single 1 1 ∧
      fderiv ℝ F y (Pi.single 2 1) 2=1 ∧
      a y 0*fderiv ℝ F y (Pi.single 2 1) 0+a y 1*fderiv ℝ F y (Pi.single 2 1) 1=0
 := by
  dsimp only
  intro hpb hQ
  have hc : ∀ z ∈ O, ∀ v, ContactTopology.FixedSurface.covector (a (F z)) (fderiv ℝ F z v)=
      L z*ContactTopology.FixedSurface.covector (a z) v := hpb
  obtain ⟨hOne,hn⟩ := ContactTopology.FixedSurface.fixed_surface_first_jet a F L O hO ha hF hL hc hfix y hy hy0 hQ
  obtain ⟨hFy,h0,h1⟩ := ContactTopology.FixedSurface.fixed_plane_derivative F O hO hF hfix y hy hy0
  refine ⟨hOne,h0,h1,hn,?_⟩
  have he := hpb y hy (Pi.single 2 1)
  rw [hFy,hOne] at he
  simp only [Pi.single_apply,Fin.reduceEq,ite_true,ite_false,mul_zero,mul_one,zero_add,add_zero,one_mul] at he
  rw [hn,mul_one] at he
  linarith [he]
