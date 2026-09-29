-- Prove2me | solution 1 for CohCarrier.injective_and_residual_of_isEis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/fb31b8df-e27c-5474-b698-03e158f1090b

import Definitions.Def_CohCarrier_Tower
import Theorems.Thm_CohCarrier_threeCopy_injective_of_isEis
import Theorems.Thm_IharaLemma_resInj_of_reduction
import Theorems.Thm_IharaLemma_resKer_localized
import Theorems.Thm_IharaLemma_square_localized
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_injective_and_residual_of_isEis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial CohCarrier

namespace IharaSolSat

variable {R : Type*} [CommRing R]

section Comb

variable {V W L : Type*}
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] [AddCommGroup L] [Module R L]

theorem resInj_comp (ϖ : R) (g : V →ₗ[R] W) (f : W →ₗ[R] L)
    (hg : ∀ (v : V) (w : W), g v = ϖ • w → ∃ v₁, v = ϖ • v₁)
    (hf : ∀ (w : W) (x : L), f w = ϖ • x → ∃ w₁, w = ϖ • w₁) :
    ∀ (v : V) (x : L), f (g v) = ϖ • x → ∃ v₁, v = ϖ • v₁ := by
  intro v x h
  obtain ⟨w₁, hw₁⟩ := hf _ _ h
  exact hg _ _ hw₁

theorem resInj_of_leftInverse (ϖ : R) (g : V →ₗ[R] W) (π : W →ₗ[R] V) (hπ : ∀ v, π (g v) = v) :
    ∀ (v : V) (w : W), g v = ϖ • w → ∃ v₁, v = ϖ • v₁ := by
  intro v w h
  exact ⟨π w, by rw [← hπ v, h, map_smul]⟩

theorem snd_snd_embComb (q : R) (T : V →ₗ[R] V) (v : V) :
    (LinearMap.snd R V V ∘ₗ LinearMap.snd R V (V × V)) (embComb q T v) = v := rfl

theorem injective_comp_embComb (q : R) (T : V →ₗ[R] V) (T' : V × V × V →ₗ[R] L)
    (hT' : Function.Injective T') : Function.Injective (T' ∘ₗ embComb q T) :=
  hT'.comp (embComb_injective q T)

theorem resInj_comp_embComb (ϖ q : R) (T : V →ₗ[R] V) (T' : V × V × V →ₗ[R] L)
    (hT' : ∀ (w : V × V × V) (x : L), T' w = ϖ • x → ∃ w₁, w = ϖ • w₁) :
    ∀ (v : V) (x : L), T' (embComb q T v) = ϖ • x → ∃ v₁, v = ϖ • v₁ :=
  resInj_comp ϖ (embComb q T) T'
    (resInj_of_leftInverse ϖ (embComb q T) (LinearMap.snd R V V ∘ₗ LinearMap.snd R V (V × V))
      (snd_snd_embComb q T)) hT'

theorem resInj_codRestrict (ϖ : R) (i : V →ₗ[R] L) (C : Submodule R L) (hC : ∀ v, i v ∈ C)
    (hi : ∀ (v : V) (x : L), i v = ϖ • x → ∃ v₁, v = ϖ • v₁) :
    ∀ (v : V) (c : C), LinearMap.codRestrict C i hC v = ϖ • c → ∃ v₁, v = ϖ • v₁ := by
  intro v c h
  exact hi v c (by simpa using congrArg Subtype.val h)

theorem injective_codRestrict (i : V →ₗ[R] L) (C : Submodule R L) (hC : ∀ v, i v ∈ C)
    (hi : Function.Injective i) : Function.Injective (LinearMap.codRestrict C i hC) :=
  fun v v' h => hi (by simpa using congrArg Subtype.val h)

end Comb

section Coeff
variable (R : Type*) [CommRing R] {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ₀ : ℕ) [NeZero ℓ₀]

theorem exists_eq_smul_of_comp (g : A →ₗ[R] B) (ϖ : R)
    (hker : ∀ a, g a = 0 → ∃ a₁, a = ϖ • a₁) (hreg : ∀ a : A, ϖ • a = 0 → a = 0)
    (φ : H1 M H A) (h : g.toAddMonoidHom.comp φ = 0) :
    ∃ ψ : H1 M H A, φ = ϖ • ψ := by
  have hx : ∀ x, ∃ a₁, φ x = ϖ • a₁ := fun x => hker _ (by
    have := congrArg (fun F => F x) h
    simpa using this)
  choose c hc using hx
  have hsub : ∀ a b : A, ϖ • a = ϖ • b → a = b := fun a b hab =>
    sub_eq_zero.mp (hreg _ (by rw [smul_sub, hab, sub_self]))
  refine ⟨{ toFun := c, map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · exact hsub _ _ (by rw [← hc, map_zero, smul_zero])
  · intro x y
    exact hsub _ _ (by rw [← hc, map_add, hc x, hc y, smul_add])
  · ext x
    exact hc x

theorem exists_eq_smul_of_cV (g : A →ₗ[R] B) (ϖ : R)
    (hker : ∀ a, g a = 0 → ∃ a₁, a = ϖ • a₁) (hreg : ∀ a : A, ϖ • a = 0 → a = 0)
    (cV : Car R A M H ℓ₀ →ₗ[R[X]] Car R B M H ℓ₀)
    (hcV : ∀ φ : H1 M H A, cV (Module.AEval'.of (heckeTLin R A M H ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R B M H ℓ₀) (g.toAddMonoidHom.comp φ))
    (v : Car R A M H ℓ₀) (h : cV v = 0) :
    ∃ v₁ : Car R A M H ℓ₀, v = (C ϖ : R[X]) • v₁ := by
  obtain ⟨φ, rfl⟩ := (Module.AEval'.of (heckeTLin R A M H ℓ₀)).surjective v
  rw [hcV] at h
  have h' : g.toAddMonoidHom.comp φ = 0 :=
    (Module.AEval'.of (heckeTLin R B M H ℓ₀)).injective (h.trans (map_zero _).symm)
  obtain ⟨ψ, rfl⟩ := exists_eq_smul_of_comp R M H g ϖ hker hreg φ h'
  exact ⟨Module.AEval'.of (heckeTLin R A M H ℓ₀) ψ, by
    rw [LinearEquiv.map_smul, Polynomial.C_eq_algebraMap, algebraMap_smul]⟩

theorem C_smul_eq_zero_of_coeff (ϖ : R) (hB : ∀ b : B, ϖ • b = 0) (y : Car R B M H ℓ₀) :
    (C ϖ : R[X]) • y = 0 := by
  obtain ⟨ψ, rfl⟩ := (Module.AEval'.of (heckeTLin R B M H ℓ₀)).surjective y
  have h0 : ϖ • ψ = 0 := AddMonoidHom.ext fun x => by rw [AddMonoidHom.smul_apply, hB]; rfl
  rw [Polynomial.C_eq_algebraMap, algebraMap_smul, ← LinearEquiv.map_smul, h0, map_zero]

theorem C_smul_eq_zero_localized (S : Submonoid R[X]) (ϖ : R) {L L' : Type*} [AddCommGroup L]
    [Module R[X] L] [AddCommGroup L'] [Module R[X] L'] (gL : L →ₗ[R[X]] L') [IsLocalizedModule S gL]
    (hL : ∀ y : L, (C ϖ : R[X]) • y = 0) (y' : L') : (C ϖ : R[X]) • y' = 0 := by
  obtain ⟨⟨y, s⟩, hs⟩ := IsLocalizedModule.surj S gL y'
  have hs' : (s : R[X]) • y' = gL y := by rw [← Submonoid.smul_def]; exact hs
  apply IsLocalizedModule.smul_injective gL s
  show s • ((C ϖ : R[X]) • y') = s • (0 : L')
  rw [smul_zero, Submonoid.smul_def, smul_comm, hs', ← map_smul, hL, map_zero]

end Coeff

end IharaSolSat

set_option maxHeartbeats 1600000 in
open IharaSolSat in
theorem solution
    (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero q]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
    (B : Type) [AddCommGroup B] [Module R B]
    (ϖ : R) (g : A →ₗ[R] B) (hker : ∀ a, g a = 0 → ∃ a₁, a = ϖ • a₁)
    (hreg : ∀ a : A, ϖ • a = 0 → a = 0) (hB : ∀ b : B, ϖ • b = 0)
    (rL d : Car R A N ⊤ ℓ₀ →ₗ[R[X]] Car R A (N * q) ⊤ ℓ₀)
    (i j : Car R A (N * q) ⊤ ℓ₀ →ₗ[R[X]] Car R A (N * q * q) ⊤ ℓ₀)
    (hrL : ∀ φ : H1 N ⊤ A, rL (Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R A (N * q) ⊤ ℓ₀) (iDeg' N (N * q) ⊤ ⊤ 1 A h₁ φ))
    (hd : ∀ φ : H1 N ⊤ A, d (Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R A (N * q) ⊤ ℓ₀) (iDeg' N (N * q) ⊤ ⊤ q A hq φ))
    (hi : ∀ ψ : H1 (N * q) ⊤ A, i (Module.AEval'.of (heckeTLin R A (N * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R A (N * q * q) ⊤ ℓ₀) (iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' ψ))
    (hj : ∀ ψ : H1 (N * q) ⊤ A, j (Module.AEval'.of (heckeTLin R A (N * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R A (N * q * q) ⊤ ℓ₀) (iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' ψ))
    (rLB dB : Car R B N ⊤ ℓ₀ →ₗ[R[X]] Car R B (N * q) ⊤ ℓ₀)
    (iB jB : Car R B (N * q) ⊤ ℓ₀ →ₗ[R[X]] Car R B (N * q * q) ⊤ ℓ₀)
    (hrLB : ∀ φ : H1 N ⊤ B, rLB (Module.AEval'.of (heckeTLin R B N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R B (N * q) ⊤ ℓ₀) (iDeg' N (N * q) ⊤ ⊤ 1 B h₁ φ))
    (hdB : ∀ φ : H1 N ⊤ B, dB (Module.AEval'.of (heckeTLin R B N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R B (N * q) ⊤ ℓ₀) (iDeg' N (N * q) ⊤ ⊤ q B hq φ))
    (hiB : ∀ ψ : H1 (N * q) ⊤ B, iB (Module.AEval'.of (heckeTLin R B (N * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R B (N * q * q) ⊤ ℓ₀) (iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 B h₁' ψ))
    (hjB : ∀ ψ : H1 (N * q) ⊤ B, jB (Module.AEval'.of (heckeTLin R B (N * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R B (N * q * q) ⊤ ℓ₀) (iDeg' (N * q) (N * q * q) ⊤ ⊤ q B hq' ψ))
    (cV : Car R A N ⊤ ℓ₀ →ₗ[R[X]] Car R B N ⊤ ℓ₀)
    (hcV : ∀ φ : H1 N ⊤ A, cV (Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀) φ)
      = Module.AEval'.of (heckeTLin R B N ⊤ ℓ₀) (g.toAddMonoidHom.comp φ))
    (cL : Car R A (N * q * q) ⊤ ℓ₀ →ₗ[R[X]] Car R B (N * q * q) ⊤ ℓ₀)
    (hcL : ∀ ψ : H1 (N * q * q) ⊤ A, cL (Module.AEval'.of (heckeTLin R A (N * q * q) ⊤ ℓ₀) ψ)
      = Module.AEval'.of (heckeTLin R B (N * q * q) ⊤ ℓ₀) (g.toAddMonoidHom.comp ψ))
    {VA LA VB LB : Type*} [AddCommGroup VA] [Module R[X] VA] [AddCommGroup LA] [Module R[X] LA]
    [AddCommGroup VB] [Module R[X] VB] [AddCommGroup LB] [Module R[X] LB]
    (gVA : Car R A N ⊤ ℓ₀ →ₗ[R[X]] VA) [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gVA]
    (gLA : Car R A (N * q * q) ⊤ ℓ₀ →ₗ[R[X]] LA) [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gLA]
    (gVB : Car R B N ⊤ ℓ₀ →ₗ[R[X]] VB) [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gVB]
    (gLB : Car R B (N * q * q) ⊤ ℓ₀ →ₗ[R[X]] LB) [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gLB]
    (hcoreA : ∀ g h : H1 N ⊤ A,
      iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + iDeg' N (N * q) ⊤ ⊤ q A hq h = 0 → IsEis R A N ⊤ ℓ₀ g ∧ IsEis R A N ⊤ ℓ₀ h)
    (h25A : ∀ x z' : H1 (N * q) ⊤ A,
      iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
        ∃ w : H1 N ⊤ A, IsEis R A (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
          IsEis R A (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q A hq w))
    (hcoreB : ∀ g h : H1 N ⊤ B,
      iDeg' N (N * q) ⊤ ⊤ 1 B h₁ g + iDeg' N (N * q) ⊤ ⊤ q B hq h = 0 → IsEis R B N ⊤ ℓ₀ g ∧ IsEis R B N ⊤ ℓ₀ h)
    (h25B : ∀ x z' : H1 (N * q) ⊤ B,
      iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 B h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q B hq' z' = 0 →
        ∃ w : H1 N ⊤ B, IsEis R B (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 B h₁ w) ∧
          IsEis R B (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q B hq w))
    (TA : (VA × VA × VA) →ₗ[R[X]] LA)
    (hTA : ∀ f : Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀,
      TA (gVA f.1, gVA f.2.1, gVA f.2.2) = gLA (threeCopy rL d i j f))
    (TB : (VB × VB × VB) →ₗ[R[X]] LB)
    (hTB : ∀ f : Car R B N ⊤ ℓ₀ × Car R B N ⊤ ℓ₀ × Car R B N ⊤ ℓ₀,
      TB (gVB f.1, gVB f.2.1, gVB f.2.2) = gLB (threeCopy rLB dB iB jB f))
    (rV : VA →ₗ[R[X]] VB) (hrV : ∀ v, rV (gVA v) = gVB (cV v))
    (rL2 : LA →ₗ[R[X]] LB) (hrL2 : ∀ x, rL2 (gLA x) = gLB (cL x))
    (TqV : VA →ₗ[R[X]] VA) :
    Function.Injective (TA ∘ₗ embComb (q : R[X]) TqV) ∧
      ∀ (v : VA) (x : LA), TA (embComb (q : R[X]) TqV v) = (C ϖ : R[X]) • x →
        ∃ v₁ : VA, v = (C ϖ : R[X]) • v₁ := by
  have hinjA := threeCopy_injective_of_isEis R A ℓ₀ N q h₁ hq h₁' hq' rL d i j hrL hd hi hj gVA gLA
    hcoreA h25A TA hTA
  have hinjB := threeCopy_injective_of_isEis R B ℓ₀ N q h₁ hq h₁' hq' rLB dB iB jB hrLB hdB hiB hjB
    gVB gLB hcoreB h25B TB hTB
  refine ⟨injective_comp_embComb _ TqV TA hinjA, resInj_comp_embComb (C ϖ) (q : R[X]) TqV TA ?_⟩

  have hkerV : ∀ v' : VA, rV v' = 0 → ∃ v₁, v' = (C ϖ : R[X]) • v₁ :=
    IharaLemma.resKer_localized (Submonoid.powers (tw R ℓ₀)) (C ϖ) cV
      (fun v hv => exists_eq_smul_of_cV R N ⊤ ℓ₀ g ϖ hker hreg cV hcV v hv) gVA gVB rV hrV
  have hkerW : ∀ w : VA × VA × VA, (rV.prodMap (rV.prodMap rV)) w = 0 →
      ∃ w₁, w = (C ϖ : R[X]) • w₁ := by
    rintro ⟨w₁, w₂, w₃⟩ hw
    simp only [LinearMap.prodMap_apply, Prod.mk_eq_zero] at hw
    obtain ⟨u₁, hu₁⟩ := hkerV _ hw.1
    obtain ⟨u₂, hu₂⟩ := hkerV _ hw.2.1
    obtain ⟨u₃, hu₃⟩ := hkerV _ hw.2.2
    exact ⟨(u₁, u₂, u₃), by rw [hu₁, hu₂, hu₃]; rfl⟩

  have hLB : ∀ y' : LB, (C ϖ : R[X]) • y' = 0 :=
    C_smul_eq_zero_localized R (Submonoid.powers (tw R ℓ₀)) ϖ gLB
      (C_smul_eq_zero_of_coeff R (N * q * q) ⊤ ℓ₀ ϖ hB)
  have hϖL : ∀ x : LA, rL2 ((C ϖ : R[X]) • x) = 0 := fun x => by rw [map_smul, hLB]

  have hsq0 : ∀ f : Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀,
      cL (threeCopy rL d i j f) = threeCopy rLB dB iB jB ((cV.prodMap (cV.prodMap cV)) f) := by
    rintro ⟨f₁, f₂, f₃⟩
    obtain ⟨φ₁, rfl⟩ := (Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀)).surjective f₁
    obtain ⟨φ₂, rfl⟩ := (Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀)).surjective f₂
    obtain ⟨φ₃, rfl⟩ := (Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀)).surjective f₃
    simp only [threeCopy_apply, map_add, LinearMap.prodMap_apply, hrL, hd, hi, hj, hcL, hcV, hrLB, hdB,
      hiB, hjB]
    rfl
  have hsq : ∀ w, rL2 (TA w) = TB ((rV.prodMap (rV.prodMap rV)) w) :=
    IharaLemma.square_localized (Submonoid.powers (tw R ℓ₀)) _ _ _ _ hsq0
      (gVA.prodMap (gVA.prodMap gVA)) (gVB.prodMap (gVB.prodMap gVB)) gLA gLB
      TA (fun f => hTA f) (rV.prodMap (rV.prodMap rV))
      (fun f => by simp only [LinearMap.prodMap_apply, hrV])
      rL2 hrL2 TB (fun f => hTB f)
  exact IharaLemma.resInj_of_reduction (C ϖ) TA (rV.prodMap (rV.prodMap rV)) rL2 TB hsq hkerW hϖL hinjB

#print axioms solution

end S_CohCarrier_injective_and_residual_of_isEis
end P2MW
export P2MW.S_CohCarrier_injective_and_residual_of_isEis (solution)
