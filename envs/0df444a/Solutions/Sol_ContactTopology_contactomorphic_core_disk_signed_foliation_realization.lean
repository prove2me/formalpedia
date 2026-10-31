-- Prove2me | solution 1 for ContactTopology.contactomorphic_core_disk_signed_foliation_realization
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-30T22:29:23.122635+00:00
-- url     : https://prove2.me/submissions/45da4724-bbe6-44fd-95d2-8e065a444e58

import Theorems.Thm_ContactTopology_relative_convex_disk_realization_from_signed_dividing_data
import Theorems.Thm_ContactTopology_contactomorphic_core_spanning_disk_neighborhood
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.Compact
namespace ContactTopology.Hemisphere
open Set Function
open scoped ContDiff
noncomputable section
abbrev P := Fin 2 → ℝ
def diskSq (x : P) : ℝ := x 0^2+x 1^2
def invariantVolume (u : P → ℝ) (β : P → P) (x : P) : ℝ :=
  β x 0*fderiv ℝ u x (Pi.single 1 1)-β x 1*fderiv ℝ u x (Pi.single 0 1)+
    u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0)
def beta (x : P) : P := ![1+x 0^2-x 1^2, 2*x 0*x 1]
def normal (x : P) : ℝ := 2*x 1

lemma beta_contDiff : ContDiff ℝ ∞ beta := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [beta] <;> fun_prop

lemma normal_contDiff : ContDiff ℝ ∞ normal := by unfold normal; fun_prop

lemma normal_fderiv (x v : P) : fderiv ℝ normal x v = 2*v 1 := by
  have hd := ((ContinuousLinearMap.proj 1 : P →L[ℝ] ℝ).hasFDerivAt (x := x)).const_mul 2
  change HasFDerivAt normal _ x at hd
  rw [hd.fderiv]
  simp

lemma beta_fderiv (x v : P) : fderiv ℝ beta x v =
    ![2*x 0*v 0-2*x 1*v 1,2*v 0*x 1+2*x 0*v 1] := by
  let p (i : Fin 2) : P →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h0 := ((hasFDerivAt_const (𝕜 := ℝ) (1:ℝ) x).add
    ((p 0).hasFDerivAt.pow 2)).sub ((p 1).hasFDerivAt.pow 2)
  have h1 := (((p 0).hasFDerivAt (x := x)).const_mul 2).mul ((p 1).hasFDerivAt (x := x))
  change HasFDerivAt (fun z : P => 1+z 0^2-z 1^2) _ x at h0
  change HasFDerivAt (fun z : P => 2*z 0*z 1) _ x at h1
  have hD : HasFDerivAt beta (ContinuousLinearMap.pi
      ![fderiv ℝ (fun z : P => 1+z 0^2-z 1^2) x,
        fderiv ℝ (fun z : P => 2*z 0*z 1) x]) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0.differentiableAt.hasFDerivAt
    · exact h1.differentiableAt.hasFDerivAt
  rw [hD.fderiv]
  ext i
  fin_cases i <;> simp [h0.fderiv,h1.fderiv,p] <;> ring

lemma model_volume (x : P) : invariantVolume normal beta x=2*(1+x 0^2+3*x 1^2) := by
  simp [invariantVolume,normal_fderiv,beta_fderiv,beta,normal]
  ring

lemma model_positive (x : P) : 0 < invariantVolume normal beta x := by
  rw [model_volume]
  positivity

lemma model_legendrian_boundary (x : P) (hx : diskSq x=1) :
    beta x 0*(-x 1)+beta x 1*x 0=0 := by
  dsimp [diskSq] at hx
  calc beta x 0*(-x 1)+beta x 1*x 0 = x 1*(x 0^2+x 1^2-1) := by simp [beta]; ring
    _ = 0 := by rw [hx]; ring

end
end ContactTopology.Hemisphere


open Set Function Topology
open scoped ContDiff
theorem solution
    (F : BirkhoffGlobalSection.EquivariantSphereContactomorphism)
    (β : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (hβ : ContDiff ℝ ∞ β)
    (K : Set (Fin 2 → ℝ)) (hK : IsCompact K) (hKD : K ⊆ {x | x 0^2+x 1^2 < 1})
    (heq : ∀ x, x ∉ K → β x = ![1+x 0^2-x 1^2,2*x 0*x 1])
    (hdiv : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → x 1 ≠ 0 →
      0 < x 1*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0))
    (hcross : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → x 1=0 → 0 < β x 0)
    (U : Set (Fin 4 → ℝ)) (hU : IsOpen U)
    (hDU : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → F.toFun
      ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
        (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0] ∈ U) :
    let d : (Fin 2 → ℝ) → (Fin 4 → ℝ) := fun x =>
      F.toFun ![2*x 0/(1+x 0^2+x 1^2),2*x 1/(1+x 0^2+x 1^2),
        (1-x 0^2-x 1^2)/(1+x 0^2+x 1^2),0]
    ∃ K' : Set (Fin 2 → ℝ), IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ {x | x 0^2+x 1^2 < 1} ∧
    ∃ k : ℝ → (Fin 2 → ℝ) → (Fin 4 → ℝ), ∃ r : (Fin 2 → ℝ) → ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × (Fin 2 → ℝ) => k p.1 p.2) ∧ ContDiff ℝ ∞ r ∧
      (∀ x, 0 < r x) ∧ (∀ t x, k t x ∈ BirkhoffGlobalSection.unitThreeSphere) ∧
      (∀ x, k 0 x=d x) ∧ (∀ t x, x ∉ K' → k t x=d x) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → x 1=0 → k t x=d x) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → k t x ∈ U) ∧
      (∀ t, Topology.IsEmbedding (fun x : {x : (Fin 2 → ℝ) // x 0^2+x 1^2 ≤ 1} => k t x)) ∧
      (∀ t x, x 0^2+x 1^2 ≤ 1 → Function.Injective (fderiv ℝ (k t) x)) ∧
      (∀ t x, x 0^2+x 1^2=1 → k t x=F.toFun ![x 0,x 1,0,0]) ∧
      (∀ t x, x 0^2+x 1^2=1 → BirkhoffGlobalSection.phaseRadialContact (k t x)
        (fderiv ℝ (k t) x ![-x 1,x 0])=0) ∧
      ∀ x, x 0^2+x 1^2 ≤ 1 → ∀ v,
        BirkhoffGlobalSection.phaseRadialContact (k 1 x) (fderiv ℝ (k 1) x v) =
          r x*(β x 0*v 0+β x 1*v 1)
 := by
  dsimp only
  obtain ⟨C,R,r,N,hC,hr,hpos,hN,hDN,hSphere,hstart,hEmb,hInv,hpb,hRight,hDivide,hLeg⟩ :=
    ContactTopology.contactomorphic_core_spanning_disk_neighborhood F
  let u : (Fin 2 → ℝ) → ℝ := ContactTopology.Hemisphere.normal
  let β₀ : (Fin 2 → ℝ) → (Fin 2 → ℝ) := ContactTopology.Hemisphere.beta
  have hu := ContactTopology.Hemisphere.normal_contDiff
  have hβ₀ := ContactTopology.Hemisphere.beta_contDiff
  have hdiv' : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → u x ≠ 0 →
      0 < u x*(fderiv ℝ β x (Pi.single 0 1) 1-fderiv ℝ β x (Pi.single 1 1) 0) := by
    intro x hx hn
    have hb : x 1 ≠ 0 := by intro hb; apply hn; simp [u,ContactTopology.Hemisphere.normal,hb]
    have hh := hdiv x hx hb
    change 0 < (2*x 1)*_
    nlinarith
  have hcross' : ∀ x : Fin 2 → ℝ, x 0^2+x 1^2 ≤ 1 → u x=0 →
      fderiv ℝ u x ![β x 1,-β x 0] < 0 := by
    intro x hx hn
    have hb : x 1=0 := by simpa [u,ContactTopology.Hemisphere.normal] using hn
    rw [ContactTopology.Hemisphere.normal_fderiv]
    simp
    linarith [hcross x hx hb]
  let W : Set (Fin 3 → ℝ) := N ∩ C ⁻¹' U
  have hW : IsOpen W := hN.inter (hU.preimage hC.continuous)
  have hDW (x : Fin 2 → ℝ) (hx : x 0^2+x 1^2 ≤ 1) : (![x 0,x 1,0] : Fin 3 → ℝ) ∈ W := by
    refine ⟨hDN x hx,?_⟩
    change C ![x 0,x 1,0] ∈ U
    rw [hstart]
    exact hDU x hx
  obtain ⟨K',hK',hKK',hK'D,k,s,hk,hs,hspos,hk0,hkfix,hkdiv,hkW,hkEmb,hkDer,hkLeg,hkEnd,hkFields⟩ :=
    ContactTopology.relative_convex_disk_realization_from_signed_dividing_data
      Set.univ isOpen_univ (fun _ _ => Set.mem_univ _) u β₀ β hu.contDiffOn hβ₀.contDiffOn hβ.contDiffOn
      hdiv' hcross' ContactTopology.Hemisphere.model_legendrian_boundary K hK hKD
      (fun x _ hx => heq x hx) W hW hDW
      (fun x _ => ContactTopology.Hemisphere.model_positive x)
  let L : ℝ → (Fin 2 → ℝ) → (Fin 4 → ℝ) := fun t x => C (k t x)
  have hL : ContDiff ℝ ∞ (fun p : ℝ × (Fin 2 → ℝ) => L p.1 p.2) := hC.comp hk
  have hks (t : ℝ) : ContDiff ℝ ∞ (k t) := hk.comp (contDiff_const.prodMk contDiff_id)
  let ρ : (Fin 2 → ℝ) → ℝ := fun x => r (k 1 x)*s x
  have hρ : ContDiff ℝ ∞ ρ := (hr.comp (hks 1)).mul hs
  have hNmem (t : ℝ) (x : Fin 2 → ℝ) (hx : x 0^2+x 1^2 ≤ 1) : k t x ∈ N :=
    (hkW t x hx).2.1
  have hCD (t : ℝ) (x v : Fin 2 → ℝ) :
      fderiv ℝ (L t) x v=fderiv ℝ C (k t x) (fderiv ℝ (k t) x v) := by
    exact congrArg (fun D : (Fin 2 → ℝ) →L[ℝ] (Fin 4 → ℝ) => D v)
      (fderiv_comp x (hC.differentiable (by simp) _) ((hks t).differentiable (by simp) x))
  refine ⟨K',hK',hKK',hK'D,L,ρ,hL,hρ,fun x => mul_pos (hpos _) (hspos x),
    fun t x => hSphere _,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x
    change C (k 0 x)=_
    rw [hk0,hstart]
  · intro t x hx
    change C (k t x)=_
    rw [hkfix t x hx,hstart]
  · intro t x hx hb
    change C (k t x)=_
    rw [hkdiv t x hx (by simp [u,ContactTopology.Hemisphere.normal,hb]),hstart]
  · intro t x hx
    exact (hkW t x hx).2.2
  · intro t
    have hE := (hkEmb t).codRestrict N (fun x => hNmem t x.val x.property)
    exact hEmb.comp hE
  · intro t x hx
    have h1 := (hInv (k t x) (hNmem t x hx)).2.2
    intro v w hvw
    apply hkDer t x hx
    apply h1
    simpa only [hCD] using hvw
  · intro t x hx
    have hout : x ∉ K' := by intro hc; have hh := hK'D hc; exact (lt_irrefl (1:ℝ)) (hx ▸ hh)
    change C (k t x)=_
    rw [hkfix t x hout,hstart]
    congr 1
    have hx' : 1+x 0^2+x 1^2=2 := by linarith
    ext i
    fin_cases i <;> simp [hx'] <;> linarith
  · intro t x hx
    rw [hCD,hpb _ (hNmem t x hx.le)]
    have hh := hkLeg t x hx
    change _+_+_=0 at hh
    change r (k t x)*(_+_+_)=0
    convert! mul_eq_zero_of_right (r (k t x)) hh using 1 <;>
      simp [β₀,u,ContactTopology.Hemisphere.beta,ContactTopology.Hemisphere.normal]
  · intro x hx v
    rw [hCD,hpb _ (hNmem 1 x hx)]
    have hh := hkEnd x hx v
    change _+_+_=s x*(β x 0*v 0+β x 1*v 1) at hh
    change r (k 1 x)*(_+_+_)=_
    have he : (1+(k 1 x) 0^2-(k 1 x) 1^2)*(fderiv ℝ (k 1) x v) 0+
        (2*(k 1 x) 0*(k 1 x) 1)*(fderiv ℝ (k 1) x v) 1+
        (2*(k 1 x) 1)*(fderiv ℝ (k 1) x v) 2 = s x*(β x 0*v 0+β x 1*v 1) := hh
    rw [he]
    dsimp [ρ]
    ring
