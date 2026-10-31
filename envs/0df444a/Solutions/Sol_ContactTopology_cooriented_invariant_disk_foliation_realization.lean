-- Prove2me | solution 1 for ContactTopology.cooriented_invariant_disk_foliation_realization
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T20:29:28.746767+00:00
-- url     : https://prove2.me/submissions/9f77d485-5330-4007-bcf0-7cfc35ee0f32

import Theorems.Thm_DifferentialTopology_positive_ratio_of_cooriented_regular_defining_functions
import Theorems.Thm_ContactTopology_local_legendrian_boundary_disk_foliation_realization
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ContactTopology.Normalization
open Set Filter Function Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

abbrev P := Fin 2 → ℝ
abbrev V := Fin 3 → ℝ

def volume (u : P → ℝ) (β : P → P) (x : P) : ℝ :=
  β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
    u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)

lemma precomp_equiv_derivative_ne_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (u : F → ℝ) (hu : ContDiff ℝ ∞ u) (p : E)
    (hD : fderiv ℝ u (e p) ≠ 0) : fderiv ℝ (fun x => u (e x)) p ≠ 0 := by
  have hd := (hu.differentiable (by simp) (e p)).hasFDerivAt.comp p e.hasFDerivAt
  change HasFDerivAt (fun x => u (e x)) _ p at hd
  intro hz
  apply hD
  apply ContinuousLinearMap.ext
  intro w
  obtain ⟨z,rfl⟩ := e.surjective w
  have he := congrArg (fun D : E →L[ℝ] ℝ => D z) (hd.fderiv.symm.trans hz)
  simpa using he

lemma positive_ratio_finTwo (u v : P → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hregu : ∀ x, u x = 0 → fderiv ℝ u x ≠ 0)
    (hregv : ∀ x, v x = 0 → fderiv ℝ v x ≠ 0)
    (hzero : ∀ x, u x = 0 ↔ v x = 0) (hsign : ∀ x, v x ≠ 0 → 0 < u x*v x) :
    ∃ a : P → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 < a x) ∧ ∀ x, u x = a x*v x := by
  let e : P ≃L[ℝ] (ℝ × ℝ) := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  let U : (ℝ × ℝ) → ℝ := fun x => u (e.symm x)
  let W : (ℝ × ℝ) → ℝ := fun x => v (e.symm x)
  have hU : ContDiff ℝ ∞ U := hu.comp e.symm.contDiff
  have hW : ContDiff ℝ ∞ W := hv.comp e.symm.contDiff
  obtain ⟨a,ha,hunique⟩ := DifferentialTopology.positive_ratio_of_cooriented_regular_defining_functions U W hU hW
    (fun x hx => precomp_equiv_derivative_ne_zero e.symm u hu x (hregu _ hx))
    (fun x hx => precomp_equiv_derivative_ne_zero e.symm v hv x (hregv _ hx))
    (fun x => hzero (e.symm x)) (fun x hx => hsign (e.symm x) hx)
  refine ⟨fun x => a (e x),ha.1.comp e.contDiff,fun x => ha.2.1 _,?_⟩
  intro x
  simpa only [U,W,e.symm_apply_apply] using ha.2.2 (e x)

lemma volume_regular_zero (u : P → ℝ) (β : P → P) (hpos : ∀ x, 0 < volume u β x) :
    ∀ x, u x = 0 → fderiv ℝ u x ≠ 0 := by
  intro x hx hd
  have hp := hpos x
  simp [volume,hx,hd] at hp

lemma volume_scale (u : P → ℝ) (β : P → P) (a : P → ℝ)
    (hu : ContDiff ℝ ∞ u) (hβ : ContDiff ℝ ∞ β) (ha : ContDiff ℝ ∞ a) (x : P) :
    volume (fun y => a y*u y) (fun y => a y • β y) x = a x^2*volume u β x := by
  have hdu := ((ha.differentiable (by simp) x).hasFDerivAt.mul
    (hu.differentiable (by simp) x).hasFDerivAt).fderiv
  have hdβ := ((ha.differentiable (by simp) x).hasFDerivAt.smul
    (hβ.differentiable (by simp) x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y => a y*u y) x = _ at hdu
  change fderiv ℝ (fun y => a y • β y) x = _ at hdβ
  simp [volume,hdu,hdβ]
  ring

lemma factor_eq_one_on_open (u v a : P → ℝ) (hv : ContDiff ℝ ∞ v) (ha : ContDiff ℝ ∞ a)
    (hreg : ∀ x, v x = 0 → fderiv ℝ v x ≠ 0) (hfactor : ∀ x, u x = a x*v x)
    (U : Set P) (hU : IsOpen U) (heq : EqOn u v U) : ∀ x ∈ U, a x = 1 := by
  intro x hx
  by_cases hz : v x = 0
  · have hnear : u =ᶠ[𝓝 x] v := Filter.mem_of_superset (hU.mem_nhds hx) heq
    have hprod : u = (fun x => a x*v x) := funext hfactor
    have hd : a x • fderiv ℝ v x = fderiv ℝ v x := by
      calc
        a x • fderiv ℝ v x = fderiv ℝ (fun y => a y*v y) x := by
          rw [fderiv_fun_mul (ha.differentiable (by simp) x) (hv.differentiable (by simp) x)]
          simp [hz]
        _ = fderiv ℝ u x := by rw [← hprod]
        _ = fderiv ℝ v x := hnear.fderiv_eq
    have hw : ∃ w, fderiv ℝ v x w ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact hreg x hz (ContinuousLinearMap.ext hn)
    obtain ⟨w,hw⟩ := hw
    apply mul_right_cancel₀ hw
    simpa using congrArg (fun D : P →L[ℝ] ℝ => D w) hd
  · apply mul_right_cancel₀ hz
    rw [← hfactor x,heq hx,one_mul]

lemma normalize_invariant_forms (u₀ u₁ : P → ℝ) (β₀ β₁ : P → P)
    (hu₀ : ContDiff ℝ ∞ u₀) (hu₁ : ContDiff ℝ ∞ u₁)
    (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < volume u₀ β₀ x) (hpos₁ : ∀ x, 0 < volume u₁ β₁ x)
    (hzero : ∀ x, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (K : Set P) (hK : IsCompact K)
    (heq : ∀ x, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x) :
    ∃ a : P → ℝ, ContDiff ℝ ∞ a ∧ (∀ x, 0 < a x) ∧ (∀ x, u₀ x = a x*u₁ x) ∧
      ContDiff ℝ ∞ (fun x => a x • β₁ x) ∧
      (∀ x, 0 < volume u₀ (fun x => a x • β₁ x) x) ∧
      (∀ x, x ∉ K → a x = 1 ∧ a x • β₁ x = β₀ x) := by
  have hreg₀ := volume_regular_zero u₀ β₀ hpos₀
  have hreg₁ := volume_regular_zero u₁ β₁ hpos₁
  obtain ⟨a,ha,hapos,hfactor⟩ := positive_ratio_finTwo u₀ u₁ hu₀ hu₁ hreg₀ hreg₁ hzero hsign
  have hone : ∀ x, x ∉ K → a x = 1 :=
    factor_eq_one_on_open u₀ u₁ a hu₁ ha hreg₁ hfactor Kᶜ hK.isClosed.isOpen_compl
      (fun x hx => (heq x hx).1)
  refine ⟨a,ha,hapos,hfactor,ha.smul hβ₁,?_,?_⟩
  · intro x
    have huEq : u₀ = (fun x => a x*u₁ x) := funext hfactor
    rw [huEq,volume_scale u₁ β₁ a hu₁ hβ₁ ha]
    exact mul_pos (sq_pos_of_pos (hapos x)) (hpos₁ x)
  · intro x hx
    exact ⟨hone x hx,by rw [hone x hx,one_smul,(heq x hx).2]⟩

end
end ContactTopology.Normalization


namespace ContactTopology.Normalization
open Set Function Topology
open scoped ContDiff Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

theorem general_disk_foliation_realization (u₀ u₁ : P → ℝ) (β₀ β₁ : P → P)
    (hu₀ : ContDiff ℝ ∞ u₀) (hu₁ : ContDiff ℝ ∞ u₁)
    (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (hpos₀ : ∀ x, 0 < volume u₀ β₀ x) (hpos₁ : ∀ x, 0 < volume u₁ β₁ x)
    (hzero : ∀ x, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (hLegendrian : ∀ x, x 0^2+x 1^2 = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set P) (hK : IsCompact K) (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x)
    (U : Set V) (hU : IsOpen U)
    (hDU : ∀ x : P, x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : V) ∈ U) :
    let I : V → V := fun y => ![β₀ ![y 0,y 1] 0,β₀ ![y 0,y 1] 1,u₀ ![y 0,y 1]]
    let B : V → V → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    ∃ k : ℝ → P → V, ∃ R : P → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × P => k p.1 p.2) ∧ ContDiff ℝ ∞ R ∧
      (∀ x, 0 < R x) ∧ (∀ x, k 0 x = ![x 0,x 1,0]) ∧
      (∀ t x, x ∉ K → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → (k t x 0)^2+(k t x 1)^2 ≤ 1 ∧ k t x ∈ U) ∧
      (∀ t, IsEmbedding (fun x : {x : P // x 0^2+x 1^2 ≤ 1} => k t x)) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, x 0^2+x 1^2 = 1 → B (I (k t x)) (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      ∀ x, x 0^2+x 1^2 ≤ 1 → ∀ v,
        B (I (k 1 x)) (fderiv ℝ (k 1) x v) = R x*(β₁ x 0*v 0+β₁ x 1*v 1) := by
  dsimp only
  obtain ⟨a,ha,hapos,hfactor,hhat,hvolhat,heqa⟩ :=
    normalize_invariant_forms u₀ u₁ β₀ β₁ hu₀ hu₁ hβ₀ hβ₁ hpos₀ hpos₁ hzero hsign K hK heq
  obtain ⟨k,r,hk,hr,hrpos,hinit,hstat,hfix,hneigh,hemb,hinj,hLegend,hpb⟩ :=
    ContactTopology.local_legendrian_boundary_disk_foliation_realization u₀ β₀ (fun x => a x • β₁ x)
      hu₀ hβ₀ hhat hLegendrian K hK hKD (fun x hx => (heqa x hx).2) U hU hDU hpos₀ hvolhat
  refine ⟨k,fun x => r x*a x,hk,hr.mul ha,fun x => mul_pos (hrpos x) (hapos x),
    hinit,hfix,hneigh,hemb,hinj,hLegend,?_⟩
  intro x hx v
  have hp := hpb x hx v
  change _ = r x*((a x • β₁ x) 0*v 0+(a x • β₁ x) 1*v 1) at hp
  dsimp only at hp
  rw [hp]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

end
end ContactTopology.Normalization


open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem solution (u₀ u₁ : (Fin 2 → ℝ) → ℝ) (β₀ β₁ : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (hu₀ : ContDiff ℝ ∞ u₀) (hu₁ : ContDiff ℝ ∞ u₁)
    (hβ₀ : ContDiff ℝ ∞ β₀) (hβ₁ : ContDiff ℝ ∞ β₁)
    (hzero : ∀ x, u₀ x = 0 ↔ u₁ x = 0)
    (hsign : ∀ x, u₁ x ≠ 0 → 0 < u₀ x*u₁ x)
    (hLegendrian : ∀ x, x 0^2+x 1^2 = 1 → β₀ x 0*(-x 1)+β₀ x 1*x 0 = 0)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x, x ∉ K → u₀ x = u₁ x ∧ β₁ x = β₀ x)
    (U : Set (Fin 3 → ℝ)) (hU : IsOpen U)
    (hDU : ∀ x : (Fin 2 → ℝ), x 0^2+x 1^2 ≤ 1 → (![x 0,x 1,0] : (Fin 3 → ℝ)) ∈ U) :
    let Q : ((Fin 2 → ℝ) → ℝ) → ((Fin 2 → ℝ) → (Fin 2 → ℝ)) → (Fin 2 → ℝ) → ℝ := fun u β x =>
      β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
        u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
    (∀ x, 0 < Q u₀ β₀ x) → (∀ x, 0 < Q u₁ β₁ x) →
    let I : (Fin 3 → ℝ) → (Fin 3 → ℝ) := fun y => ![β₀ ![y 0,y 1] 0,β₀ ![y 0,y 1] 1,u₀ ![y 0,y 1]]
    let B : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ := fun a v => a 0*v 0+a 1*v 1+a 2*v 2
    ∃ k : ℝ → (Fin 2 → ℝ) → (Fin 3 → ℝ), ∃ R : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 2 → ℝ) => k p.1 p.2) ∧ ContDiff ℝ ∞ R ∧
      (∀ x, 0 < R x) ∧ (∀ x, k 0 x = ![x 0,x 1,0]) ∧
      (∀ t x, x ∉ K → k t x = ![x 0,x 1,0]) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → (k t x 0)^2+(k t x 1)^2 ≤ 1 ∧ k t x ∈ U) ∧
      (∀ t, Topology.IsEmbedding (fun x : {x : (Fin 2 → ℝ) // x 0^2+x 1^2 ≤ 1} => k t x)) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → Function.Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, x 0^2+x 1^2 = 1 → B (I (k t x)) (fderiv ℝ (k t) x ![-x 1,x 0]) = 0) ∧
      ∀ x, x 0^2+x 1^2 ≤ 1 → ∀ v,
        B (I (k 1 x)) (fderiv ℝ (k 1) x v) = R x*(β₁ x 0*v 0+β₁ x 1*v 1) := by
  dsimp only
  intro hpos₀ hpos₁
  exact ContactTopology.Normalization.general_disk_foliation_realization
    u₀ u₁ β₀ β₁ hu₀ hu₁ hβ₀ hβ₁ hpos₀ hpos₁ hzero hsign hLegendrian K hK hKD heq U hU hDU
