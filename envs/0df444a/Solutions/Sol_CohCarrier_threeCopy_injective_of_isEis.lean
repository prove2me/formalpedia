-- Prove2me | solution 1 for CohCarrier.threeCopy_injective_of_isEis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9dc52d80-b3f9-5271-aa77-5e5bd2f42e83

import Definitions.Def_CohCarrier_Tower
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_threeCopy_injective_of_isEis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial CohCarrier

namespace IharaSolD3

section Chase
variable {R : Type*} [CommRing R] (S : Submonoid R)
variable {V L L2 U V' L2' : Type*}
  [AddCommGroup V] [Module R V] [AddCommGroup L] [Module R L] [AddCommGroup L2] [Module R L2]
  [AddCommGroup U] [Module R U] [AddCommGroup V'] [Module R V'] [AddCommGroup L2'] [Module R L2']

theorem loc_core {X : Type*} [AddCommGroup X] [Module R X]
    (gV : V →ₗ[R] V') [IsLocalizedModule S gV] (p r : V →ₗ[R] X)
    (EV : Submodule R V) (hEV : ∀ e ∈ EV, ∃ s : S, (s : R) • e = 0)
    (HC : ∀ g h : V, p g + r h = 0 → g ∈ EV ∧ h ∈ EV)
    (E : Submodule R X) (hE : ∀ e ∈ E, ∃ s : S, (s : R) • e = 0)
    {g h : V} (hmem : p g + r h ∈ E) : gV g = 0 ∧ gV h = 0 := by
  obtain ⟨s, hs⟩ := hE _ hmem
  rw [smul_add, ← map_smul, ← map_smul] at hs
  obtain ⟨hg, hh⟩ := HC _ _ hs
  obtain ⟨s₁, hs₁⟩ := hEV _ hg
  obtain ⟨s₂, hs₂⟩ := hEV _ hh
  refine ⟨?_, ?_⟩
  · apply IsLocalizedModule.smul_injective gV (s₁ * s)
    show ((s₁ * s : S) : R) • gV g = ((s₁ * s : S) : R) • 0
    rw [smul_zero, Submonoid.coe_mul, ← map_smul, mul_smul, hs₁, map_zero]
  · apply IsLocalizedModule.smul_injective gV (s₂ * s)
    show ((s₂ * s : S) : R) • gV h = ((s₂ * s : S) : R) • 0
    rw [smul_zero, Submonoid.coe_mul, ← map_smul, mul_smul, hs₂, map_zero]

theorem threeCopy_injective_of_core_of_lemma25
    (gV : V →ₗ[R] V') [IsLocalizedModule S gV] (gL2 : L2 →ₗ[R] L2') [IsLocalizedModule S gL2]
    (rL d : V →ₗ[R] L) (i j : L →ₗ[R] L2) (c : L →ₗ[R] U) (b : V →ₗ[R] U)
    (EV : Submodule R V) (EL : Submodule R L) (EU : Submodule R U)
    (hEV : ∀ e ∈ EV, ∃ s : S, (s : R) • e = 0)
    (hEL : ∀ e ∈ EL, ∃ s : S, (s : R) • e = 0) (hEU : ∀ e ∈ EU, ∃ s : S, (s : R) • e = 0)
    (HC1 : ∀ g h : V, rL g + d h = 0 → g ∈ EV ∧ h ∈ EV)
    (HC2 : ∀ g h : V, c (rL g) + b h = 0 → g ∈ EV ∧ h ∈ EV)
    (H25 : ∀ x z' : L, i x + j z' = 0 → ∃ w : V, z' - rL w ∈ EL ∧ c x + b w ∈ EU)
    (T' : (V' × V' × V') →ₗ[R] L2')
    (hT' : ∀ f : V × V × V, T' (gV f.1, gV f.2.1, gV f.2.2) = gL2 (threeCopy rL d i j f)) :
    Function.Injective T' := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨y₁, y₂, y₃⟩ hy

  obtain ⟨⟨f₁, s₁⟩, h₁⟩ := IsLocalizedModule.surj S gV y₁
  obtain ⟨⟨f₂, s₂⟩, h₂⟩ := IsLocalizedModule.surj S gV y₂
  obtain ⟨⟨f₃, s₃⟩, h₃⟩ := IsLocalizedModule.surj S gV y₃
  have h₁' : (s₁ : R) • y₁ = gV f₁ := h₁
  have h₂' : (s₂ : R) • y₂ = gV f₂ := h₂
  have h₃' : (s₃ : R) • y₃ = gV f₃ := h₃
  have e₁ : ((s₁ : R) * s₂ * s₃) • y₁ = gV (((s₂ : R) * s₃) • f₁) := by
    rw [map_smul, ← h₁', smul_smul]; congr 1; ring
  have e₂ : ((s₁ : R) * s₂ * s₃) • y₂ = gV (((s₁ : R) * s₃) • f₂) := by
    rw [map_smul, ← h₂', smul_smul]; congr 1; ring
  have e₃ : ((s₁ : R) * s₂ * s₃) • y₃ = gV (((s₁ : R) * s₂) • f₃) := by
    rw [map_smul, ← h₃', smul_smul]

  have hTF : gL2 (threeCopy rL d i j
      (((s₂ : R) * s₃) • f₁, ((s₁ : R) * s₃) • f₂, ((s₁ : R) * s₂) • f₃)) = 0 := by
    rw [← hT']
    dsimp only
    rw [← e₁, ← e₂, ← e₃]
    have : ((((s₁ : R) * s₂ * s₃) • y₁, ((s₁ : R) * s₂ * s₃) • y₂, ((s₁ : R) * s₂ * s₃) • y₃) : V' × V' × V')
        = ((s₁ : R) * s₂ * s₃) • (y₁, y₂, y₃) := rfl
    rw [this, map_smul, hy, smul_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S gL2).mp hTF
  have ht' : (t : R) • threeCopy rL d i j
      (((s₂ : R) * s₃) • f₁, ((s₁ : R) * s₃) • f₂, ((s₁ : R) * s₂) • f₃) = 0 := ht
  rw [← map_smul, Prod.smul_mk, Prod.smul_mk] at ht'

  set F₁ : V := (t : R) • (((s₂ : R) * s₃) • f₁) with hF₁
  set F₂ : V := (t : R) • (((s₁ : R) * s₃) • f₂) with hF₂
  set F₃ : V := (t : R) • (((s₁ : R) * s₂) • f₃) with hF₃
  have hrel : i (rL F₁) + j (rL F₂ + d F₃) = 0 := by
    rw [threeCopy_apply] at ht'
    rw [map_add]; exact ht'
  obtain ⟨w, hw₁, hw₂⟩ := H25 _ _ hrel

  obtain ⟨hF₁0, hw0⟩ := loc_core S gV (c ∘ₗ rL) b EV hEV HC2 EU hEU (by simpa using hw₂)

  have hw₁' : rL (F₂ - w) + d F₃ ∈ EL := by
    have : rL (F₂ - w) + d F₃ = rL F₂ + d F₃ - rL w := by rw [map_sub]; abel
    rw [this]; exact hw₁
  obtain ⟨hF₂w, hF₃0⟩ := loc_core S gV rL d EV hEV HC1 EL hEL hw₁'
  have hF₂0 : gV F₂ = 0 := by rw [map_sub, hw0, sub_zero] at hF₂w; exact hF₂w

  have hsS : (s₁ : R) * s₂ * s₃ ∈ S := Submonoid.mul_mem _ (Submonoid.mul_mem _ s₁.2 s₂.2) s₃.2
  have kill : ∀ (y : V') (F : V), ((s₁ : R) * s₂ * s₃) • y = gV F → gV ((t : R) • F) = 0 → y = 0 := by
    intro y F hy0 hF
    apply IsLocalizedModule.smul_injective gV (t * ⟨_, hsS⟩)
    show ((t : R) * ((s₁ : R) * s₂ * s₃)) • y = ((t : R) * ((s₁ : R) * s₂ * s₃)) • 0
    rw [smul_zero, mul_smul, hy0, ← map_smul, hF]
  simp only [Prod.mk_eq_zero]
  exact ⟨kill y₁ _ e₁ hF₁0, kill y₂ _ e₂ hF₂0, kill y₃ _ e₃ hF₃0⟩

end Chase

section Etor
variable (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A]
variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ₀ : ℕ) [NeZero ℓ₀]

set_option backward.isDefEq.respectTransparency false in

def Etor : Submodule R[X] (Car R A M H ℓ₀) where
  carrier := {F | tw R ℓ₀ • F = 0}
  add_mem' := by
    intro a b ha hb
    show tw R ℓ₀ • (a + b) = 0
    rw [smul_add, ha, hb, add_zero]
  zero_mem' := by
    show tw R ℓ₀ • (0 : Car R A M H ℓ₀) = 0
    exact smul_zero _
  smul_mem' := by
    intro c x hx
    show tw R ℓ₀ • (c • x) = 0
    rw [smul_comm, hx, smul_zero]

theorem mem_Etor_iff (F : Car R A M H ℓ₀) : F ∈ Etor R A M H ℓ₀ ↔ tw R ℓ₀ • F = 0 := Iff.rfl

theorem Etor_torsion :
    ∀ e ∈ Etor R A M H ℓ₀, ∃ s : Submonoid.powers (tw R ℓ₀), (s : R[X]) • e = 0 :=
  fun _ he => ⟨⟨tw R ℓ₀, Submonoid.mem_powers _⟩, he⟩

theorem of_mem_Etor (F : H1 M H A) (hF : IsEis R A M H ℓ₀ F) :
    Module.AEval'.of (heckeTLin R A M H ℓ₀) F ∈ Etor R A M H ℓ₀ := by
  rw [mem_Etor_iff]
  exact tw_smul_of_eq_zero R A M H ℓ₀ F hF

end Etor

end IharaSolD3

set_option maxHeartbeats 1600000 in
open IharaSolD3 in
theorem solution
    (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero q]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
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
    {V' L2' : Type*} [AddCommGroup V'] [Module R[X] V'] [AddCommGroup L2'] [Module R[X] L2']
    (gV : Car R A N ⊤ ℓ₀ →ₗ[R[X]] V') [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gV]
    (gL2 : Car R A (N * q * q) ⊤ ℓ₀ →ₗ[R[X]] L2') [IsLocalizedModule (Submonoid.powers (tw R ℓ₀)) gL2]
    (hcore : ∀ g h : H1 N ⊤ A,
      iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + iDeg' N (N * q) ⊤ ⊤ q A hq h = 0 → IsEis R A N ⊤ ℓ₀ g ∧ IsEis R A N ⊤ ℓ₀ h)
    (h25 : ∀ x z' : H1 (N * q) ⊤ A,
      iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
        ∃ w : H1 N ⊤ A, IsEis R A (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
          IsEis R A (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q A hq w))
    (T' : (V' × V' × V') →ₗ[R[X]] L2')
    (hT' : ∀ f : Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀ × Car R A N ⊤ ℓ₀,
      T' (gV f.1, gV f.2.1, gV f.2.2) = gL2 (threeCopy rL d i j f)) :
    Function.Injective T' := by
  let oN := Module.AEval'.of (heckeTLin R A N ⊤ ℓ₀)
  let oL := Module.AEval'.of (heckeTLin R A (N * q) ⊤ ℓ₀)
  let oL2 := Module.AEval'.of (heckeTLin R A (N * q * q) ⊤ ℓ₀)

  have HC1 : ∀ g h : Car R A N ⊤ ℓ₀, rL g + d h = 0 →
      g ∈ Etor R A N ⊤ ℓ₀ ∧ h ∈ Etor R A N ⊤ ℓ₀ := by
    intro g h hsum
    obtain ⟨g₀, rfl⟩ : ∃ g₀, oN g₀ = g := ⟨oN.symm g, oN.apply_symm_apply g⟩
    obtain ⟨h₀, rfl⟩ : ∃ h₀, oN h₀ = h := ⟨oN.symm h, oN.apply_symm_apply h⟩
    rw [hrL, hd, ← map_add] at hsum
    obtain ⟨hg, hh⟩ := hcore g₀ h₀ (oL.injective (hsum.trans (map_zero oL).symm))
    exact ⟨of_mem_Etor R A N ⊤ ℓ₀ g₀ hg, of_mem_Etor R A N ⊤ ℓ₀ h₀ hh⟩

  have H25 : ∀ x z' : Car R A (N * q) ⊤ ℓ₀, i x + j z' = 0 →
      ∃ w : Car R A N ⊤ ℓ₀, z' - rL w ∈ Etor R A (N * q) ⊤ ℓ₀ ∧
        (LinearMap.id : Car R A (N * q) ⊤ ℓ₀ →ₗ[R[X]] Car R A (N * q) ⊤ ℓ₀) x + d w
          ∈ Etor R A (N * q) ⊤ ℓ₀ := by
    intro x z' hsum
    obtain ⟨x₀, rfl⟩ : ∃ x₀, oL x₀ = x := ⟨oL.symm x, oL.apply_symm_apply x⟩
    obtain ⟨z₀, rfl⟩ : ∃ z₀, oL z₀ = z' := ⟨oL.symm z', oL.apply_symm_apply z'⟩
    rw [hi, hj, ← map_add] at hsum
    obtain ⟨w₀, hz, hx⟩ := h25 x₀ z₀ (oL2.injective (hsum.trans (map_zero oL2).symm))
    refine ⟨oN w₀, ?_, ?_⟩
    · rw [hrL, ← map_sub]
      exact of_mem_Etor R A (N * q) ⊤ ℓ₀ _ hz
    · rw [LinearMap.id_apply, hd, ← map_add]
      exact of_mem_Etor R A (N * q) ⊤ ℓ₀ _ hx
  exact threeCopy_injective_of_core_of_lemma25 (Submonoid.powers (tw R ℓ₀)) gV gL2 rL d i j
    LinearMap.id d (Etor R A N ⊤ ℓ₀) (Etor R A (N * q) ⊤ ℓ₀) (Etor R A (N * q) ⊤ ℓ₀)
    (Etor_torsion R A N ⊤ ℓ₀) (Etor_torsion R A (N * q) ⊤ ℓ₀) (Etor_torsion R A (N * q) ⊤ ℓ₀)
    HC1 (fun g h hgh => HC1 g h hgh) H25 T' hT'

#print axioms solution

end S_CohCarrier_threeCopy_injective_of_isEis
end P2MW
export P2MW.S_CohCarrier_threeCopy_injective_of_isEis (solution)
