-- Prove2me | solution 1 for CompanionTheory.D.LK.multAlg_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:24.673152+00:00
-- url     : https://prove2.me/submissions/0e89c88e-6008-42c6-8afa-66d3fd00ea2b

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOnePOf
import Theorems.Thm_CompanionTheory_D_LK_evK_allT
import Theorems.Thm_CompanionTheory_D_LK_evd_eig
import Theorems.Thm_CompanionTheory_D_LK_cyc_stab
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.LK
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight CasK Cas)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsDS rhoC)
open CompanionTheory.D.DSIC (KRel KUnit KStab LowSpan HWMap)
variable {n : ℕ}
namespace CompanionTheory.D.LK
theorem _root_.solution (hL : LowSpan) (hH : HWMap) (hD : Dens) (hI : InvLift) (hC : HCdec) (hG : GenCO) (hT : TopCycle)
    (hJ : Inj) : MultAlg := by
  intro n ε lam V _ _ E hlam hGl hU hLF hIM v w hv0 hv hw hwc
  have hKE : CompanionTheory.D.DSIC.KRel ε E := fun a b c d _ _ => hGl a b c d
  obtain ⟨S, hSfd, hSst, hvS⟩ := hLF v
  obtain ⟨L, hLS, hvL, hLst, hLirr, -, hLuniq⟩ := hL n ε V E (lowK ε lam) v S hKE hU hv0 hv hSfd hSst hvS
  have hLfd : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLS
  let ET : Fin n → Fin n → Module.End ℂ L := fun a b =>
    if h : ε a = ε b then (E a b).restrict (fun x hx => hLst a b h x hx) else 0
  have hET : ∀ a b (h : ε a = ε b) (x : L), ((ET a b x : L) : V) = E a b x := by
    intro a b h x
    simp only [ET, dif_pos h, LinearMap.coe_restrict_apply]
  have kET : CompanionTheory.D.DSIC.KRel ε ET := by
    intro a b c d hab hcd
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    have key := LinearMap.congr_fun (hGl a b c d) (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub] at key ⊢
    rw [hET a b hab, hET c d hcd x, hET c d hcd, hET a b hab x]
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · have e1 : ε a = ε d := by rw [h1] at hab; exact hab.trans hcd
      have e2 : ε c = ε b := by rw [h2] at hcd; exact hcd.trans hab
      rw [if_pos h1, if_pos h2] at key ⊢
      rw [hET a d e1, hET c b e2]
      exact key
    · have e1 : ε a = ε d := by rw [h1] at hab; exact hab.trans hcd
      rw [if_pos h1, if_neg h2] at key ⊢
      rw [hET a d e1]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at key ⊢
      exact key
    · have e2 : ε c = ε b := by rw [h2] at hcd; exact hcd.trans hab
      rw [if_neg h1, if_pos h2] at key ⊢
      rw [hET c b e2]
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at key ⊢
      exact key
    · rw [if_neg h1, if_neg h2] at key ⊢
      simp only [LinearMap.zero_apply, ZeroMemClass.coe_zero] at key ⊢
      exact key
  have uET : CompanionTheory.D.DSIC.KUnit ε ET := by
    intro a b h x y
    rw [Submodule.coe_inner, Submodule.coe_inner, hET a b h, hET b a h.symm]
    exact hU a b h x y
  let v' : L := ⟨v, hvL⟩
  have hv'0 : v' ≠ 0 := fun h0 => hv0 (congrArg Subtype.val h0)
  have hv' : KHighest ε ET (lowK ε lam) v' := by
    refine ⟨fun a => ?_, fun a b hab h => ?_⟩
    · apply Subtype.ext
      rw [hET a a rfl, Submodule.coe_smul]
      exact hv.1 a
    · apply Subtype.ext
      rw [hET a b h, ZeroMemClass.coe_zero]
      exact hv.2 a b hab h
  obtain ⟨S2, hS2fd, hS2st, hwS2⟩ := hLF w
  obtain ⟨φ, hφv, hφ⟩ := hH n ε L V ET E (lowK ε lam) v' w S2 kET uET hKE hU hv'0 hv' hw hS2fd hS2st hwS2
  have hφc : ∀ s : L, φ s ∈ Cyc E v := by
    let L' : Submodule ℂ V := Submodule.map L.subtype ((Cyc E v).comap φ)
    have hL'L : L' ≤ L := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2
    have hL'st : CompanionTheory.D.DSIC.KStab ε E L' := by
      rintro a b h _ ⟨s, hs, rfl⟩
      refine ⟨ET a b s, ?_, hET a b h s⟩
      show φ (ET a b s) ∈ Cyc E v
      rw [hφ a b h s]
      exact cyc_stab a b (show φ s ∈ Cyc E v from hs)
    have hvL' : v ∈ L' := ⟨v', show φ v' ∈ Cyc E v by rw [hφv]; exact hwc, rfl⟩
    rcases hLirr L' hL'L hL'st with h0 | h0
    · exfalso
      have hb0 : v ∈ (⊥ : Submodule ℂ V) := h0 ▸ hvL'
      exact hv0 ((Submodule.mem_bot ℂ).1 hb0)
    · intro s
      have hs : (s : V) ∈ L' := by rw [h0]; exact s.2
      obtain ⟨s', hs', hss'⟩ := hs
      have : s' = s := Subtype.ext hss'
      rw [← this]
      exact hs'
  obtain ⟨-, hDφ⟩ := hD n ε V E (lowK ε lam) v L hKE hU hv0 hvL hv.1 hLfd hLst hLirr hLuniq
  obtain ⟨a, ha⟩ := hDφ φ hφc
  have hcomm : ∀ c d, ε c = ε d → ∀ s ∈ L, E c d (ev E a s) = ev E a (E c d s) := by
    intro c d h s hs
    have e1 : ev E a s = φ ⟨s, hs⟩ := ha ⟨s, hs⟩
    have e2 : ev E a (E c d s) = φ (ET c d ⟨s, hs⟩) := by
      rw [← ha (ET c d ⟨s, hs⟩), hET c d h]
    rw [e1, e2, hφ c d h]
  obtain ⟨a', ha'inv, ha'⟩ := hI n ε V E L a hGl hLst hcomm
  have hwa : ev E a' v = w := by
    rw [ha' v hvL]
    exact (ha v').trans hφv
  obtain ⟨b, hb⟩ := hC n a' (fun V' _ _ E' hGl' c => ha'inv V' E' hGl' c c rfl)
  obtain ⟨-, hTop⟩ := hT n ε V E (lowK ε lam) v
  obtain ⟨hbd0, hWt⟩ := hTop hv
  have hfilt : ∀ A : Finset (CompanionTheory.D.LK.Pos n), Pi.single (M := fun _ => V) (CompanionTheory.D.LK.om ε) v A ≠ 0 → A = CompanionTheory.D.LK.om ε := by
    intro A hA
    by_contra hne
    apply hA
    rw [Pi.single_apply, if_neg hne]
  have hSup : CompanionTheory.D.LK.Sup (CompanionTheory.D.LK.allT n) ∅ (CompanionTheory.D.LK.om ε).card (Pi.single (CompanionTheory.D.LK.om ε) v) := by
    intro A hA
    rw [hfilt A hA]
    refine ⟨Finset.filter_false_of_mem (fun i _ hi => hi rfl), ?_⟩
    rw [Finset.filter_true_of_mem (fun i _ => rfl)]
  have hRef : CompanionTheory.D.LK.Ref (CompanionTheory.D.LK.allT n) ε (Pi.single (CompanionTheory.D.LK.om ε) v) := by
    intro A hA i hi _
    rw [hfilt A hA] at hi
    exact (Finset.mem_filter.1 hi).2
  obtain ⟨y, hySup, hy⟩ := hG n (CompanionTheory.D.LK.allT n) ε a' b (fun _ _ _ => rfl)
    (fun V' _ _ E' hK' => by
      have hGl' : GlRel E' := fun a b c d => hK' a b c d rfl rfl
      rw [evK_allT]
      exact ⟨fun i hi => ha'inv V' E' hGl' _ _ hi, fun x => hb V' E' hGl' x⟩)
    V E (fun a b c d _ _ => hGl a b c d) ∅ _ _ hSup hRef hbd0
  rw [evK_allT] at hy
  have hev : CompanionTheory.D.LK.evd (CompanionTheory.D.LK.Ft (CompanionTheory.D.LK.allT n) E) b (Pi.single (CompanionTheory.D.LK.om ε) v)
      = FreeAlgebra.lift ℂ (fun c => (((lowK ε lam + (2 : ℝ) • rhoC ε) c : ℝ) : ℂ)) b • Pi.single (CompanionTheory.D.LK.om ε) v :=
    evd_eig _ _ _ (fun c => hWt c) b
  have hlift : CompanionTheory.D.LK.lift n (ev E a') (Pi.single (CompanionTheory.D.LK.om ε) v) = Pi.single (CompanionTheory.D.LK.om ε) w := by
    funext A
    rw [CompanionTheory.D.LK.lift_apply]
    by_cases hA : A = CompanionTheory.D.LK.om ε
    · subst hA
      rw [Pi.single_eq_same, Pi.single_eq_same, hwa]
    · rw [Pi.single_eq_of_ne hA, Pi.single_eq_of_ne hA, map_zero]
  set β := FreeAlgebra.lift ℂ (fun c => (((lowK ε lam + (2 : ℝ) • rhoC ε) c : ℝ) : ℂ)) b
  rw [hlift, hev] at hy
  have hu : w - β • v = 0 := by
    refine hJ n ε lam V E hlam hGl hU hLF hIM (w - β • v) y (fun a => ?_) hySup ?_
    · rw [map_sub, map_smul, hw.1 a, hv.1 a, smul_sub, smul_comm]
    · rw [← hy, Pi.single_sub, Pi.single_smul']
  exact ⟨β, sub_eq_zero.1 hu⟩
end CompanionTheory.D.LK
