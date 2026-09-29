-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d241db99-790b-5f12-a5ba-dd9c9a78ae4f

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image

set_option autoImplicit false

universe u

noncomputable section

namespace P2mLieBC

open CerednikDrinfeld MvFormalGroup

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_pow_ne : ∃ ζ : GaloisField p 2, ζ ^ p ≠ ζ := by
  classical
  haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  refine ⟨(g : GaloisField p 2), fun hfix => ?_⟩
  have hcardF : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 two_ne_zero
  have hord : orderOf g = p ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, Fintype.card_units, hcardF]
  have hgp : g ^ (p - 1) = 1 := by
    apply Units.ext
    have h1 : (g : GaloisField p 2) ^ (p - 1) * (g : GaloisField p 2) = (g : GaloisField p 2) := by
      rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, hfix]
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact (mul_left_eq_self₀.mp h1).resolve_right g.ne_zero
  have hdvd : orderOf g ∣ p - 1 := orderOf_dvd_of_pow_eq_one hgp
  rw [hord] at hdvd
  have hle := Nat.le_of_dvd (by have := hp.out.two_le; omega) hdvd
  have : p * p ≤ p := by
    have := hp.out.two_le
    rw [pow_two] at hle; omega
  nlinarith [hp.out.two_le]

theorem isUnit_teichmuller_sub {ζ : GaloisField p 2} (h : ζ ^ p ≠ ζ) :
    IsUnit (WittVector.teichmuller p ζ - WittVector.frobenius (WittVector.teichmuller p ζ) : Zp2 p) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  have hz' : WittVector.frobenius (WittVector.teichmuller p ζ) = WittVector.teichmuller p (ζ ^ p) := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  have := WittVector.add_coeff_zero
    (WittVector.teichmuller p ζ - WittVector.frobenius (WittVector.teichmuller p ζ) : Zp2 p)
    (WittVector.frobenius (WittVector.teichmuller p ζ))
  rw [sub_add_cancel, hz', WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at this
  rw [hz', eq_sub_of_add_eq this.symm]
  exact sub_ne_zero.mpr (Ne.symm h)

section main

variable {B S : Type u} [CommRing B] [CommRing S]

theorem linearPart_seriesMap (g : B →+* S) (φ : SpecialFormal.Series B) :
    MvFormalGroup.linearPart (φ.map g) = (MvFormalGroup.linearPart φ).map g := by
  ext i k
  simp [MvFormalGroup.linearPart, SpecialFormal.Series.map, MvPowerSeries.coeff_map]

theorem lieAct_map_apply (g : B →+* S) (X : FormalODModule p B) (a : Zp2 p) (m : X.Lie) :
    (X.map g).lieAct a (fun i => g (m i)) = fun i => g (X.lieAct a m i) := by
  funext i
  show ((MvFormalGroup.linearPart ((X.map g).act a)).mulVec (fun i => g (m i))) i =
    g ((MvFormalGroup.linearPart (X.act a)).mulVec m i)
  rw [FormalODModule.map_act, linearPart_seriesMap, RingHom.map_mulVec]
  rfl

theorem mem_lieZero_iff (j : Zp2 p →+* B) (X : FormalODModule p B) (m : X.Lie) :
    m ∈ X.lieZero j ↔ ∀ a, X.lieAct a m = j a • m := by
  simp only [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_lieOne_iff (j : Zp2 p →+* B) (X : FormalODModule p B) (m : X.Lie) :
    m ∈ X.lieOne j ↔ ∀ a, X.lieAct a m = j (WittVector.frobenius a) • m := by
  simp only [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

variable (j : Zp2 p →+* B) (g : B →+* S) (X : FormalODModule p B)

abbrev gv : X.Lie → (X.map g).Lie := fun m i => g (m i)

theorem image_lieZero_subset : (gv g X) '' (X.lieZero j : Set X.Lie) ⊆ ((X.map g).lieZero (g.comp j) : Set _) := by
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, mem_lieZero_iff] at hm ⊢
  intro a
  rw [lieAct_map_apply, hm a]
  funext i; simp [Pi.smul_apply]

theorem image_lieOne_subset : (gv g X) '' (X.lieOne j : Set X.Lie) ⊆ ((X.map g).lieOne (g.comp j) : Set _) := by
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, mem_lieOne_iff] at hm ⊢
  intro a
  rw [lieAct_map_apply, hm a]
  funext i; simp [Pi.smul_apply]

theorem span_le_zero : Submodule.span S ((gv g X) '' (X.lieZero j : Set X.Lie)) ≤ (X.map g).lieZero (g.comp j) :=
  Submodule.span_le.mpr (image_lieZero_subset j g X)

theorem span_le_one : Submodule.span S ((gv g X) '' (X.lieOne j : Set X.Lie)) ≤ (X.map g).lieOne (g.comp j) :=
  Submodule.span_le.mpr (image_lieOne_subset j g X)

theorem lieZero_inf_lieOne_eq_bot {T : Type u} [CommRing T] (k : Zp2 p →+* T) (Y : FormalODModule p T) :
    Y.lieZero k ⊓ Y.lieOne k = ⊥ := by
  rw [eq_bot_iff]
  intro m hm
  rw [Submodule.mem_inf] at hm
  obtain ⟨h0, h1⟩ := hm
  rw [mem_lieZero_iff] at h0
  rw [mem_lieOne_iff] at h1
  obtain ⟨ζ, hζ⟩ := exists_pow_ne (p := p)
  set z : Zp2 p := WittVector.teichmuller p ζ
  have hu := isUnit_teichmuller_sub (p := p) hζ
  have hku : IsUnit (k (z - WittVector.frobenius z)) := hu.map k
  have hm0 : k (z - WittVector.frobenius z) • m = 0 := by
    rw [map_sub, sub_smul, ← h0 z, ← h1 z, sub_self]
  rw [Submodule.mem_bot]
  exact (hku.smul_left_cancel).mp (by rw [hm0, smul_zero])

theorem span_sup_span_eq_top (hc : IsCompl (X.lieZero j) (X.lieOne j)) :
    Submodule.span S ((gv g X) '' (X.lieZero j : Set X.Lie)) ⊔
      Submodule.span S ((gv g X) '' (X.lieOne j : Set X.Lie)) = ⊤ := by
  rw [eq_top_iff]

  have hbasis : ∀ v : (X.map g).Lie, v ∈ Submodule.span S (Set.range fun i : Fin 2 => (gv g X) (Pi.single i 1)) := by
    intro v
    have : v = ∑ i : Fin 2, v i • (gv g X) (Pi.single i 1) := by
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Fin.sum_univ_two]
      fin_cases k <;> simp [gv, Pi.single_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro v _
  refine Submodule.span_le.mpr ?_ (hbasis v)
  rintro _ ⟨i, rfl⟩

  have htop : (Pi.single i (1 : B) : X.Lie) ∈ X.lieZero j ⊔ X.lieOne j := by
    rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨x0, hx0, x1, hx1, hsum⟩ := Submodule.mem_sup.mp htop
  have : (gv g X) (Pi.single i 1) = (gv g X) x0 + (gv g X) x1 := by
    rw [← hsum]; funext k; simp [gv, Pi.add_apply]
  show gv g X (Pi.single i 1) ∈ _
  rw [this]
  exact Submodule.add_mem_sup (Submodule.subset_span ⟨x0, hx0, rfl⟩) (Submodule.subset_span ⟨x1, hx1, rfl⟩)

theorem eq_of_le_of_sup_top_of_inf_bot {M : Type*} [AddCommGroup M] [Module S M]
    {L0 L1 E0 E1 : Submodule S M} (h0 : L0 ≤ E0) (h1 : L1 ≤ E1) (hsup : L0 ⊔ L1 = ⊤) (hinf : E0 ⊓ E1 = ⊥) :
    L0 = E0 := by
  refine le_antisymm h0 fun x hx => ?_
  have : x ∈ L0 ⊔ L1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨l0, hl0, l1, hl1, rfl⟩ := Submodule.mem_sup.mp this
  have hl1E0 : l1 ∈ E0 := by
    have := Submodule.sub_mem E0 hx (h0 hl0)
    rwa [add_sub_cancel_left] at this
  have : l1 ∈ E0 ⊓ E1 := Submodule.mem_inf.mpr ⟨hl1E0, h1 hl1⟩
  rw [hinf, Submodule.mem_bot] at this
  rw [this, add_zero]; exact hl0

end main

end P2mLieBC

end

open CerednikDrinfeld P2mLieBC in
theorem solution
    (p : ℕ) [Fact p.Prime] {B S : Type u} [CommRing B] [CommRing S] (j : CerednikDrinfeld.Zp2 p →+* B)
    (g : B →+* S) (X : CerednikDrinfeld.FormalODModule p B) :
    (Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieZero j : Set X.Lie)) ≤
        (X.map g).lieZero (g.comp j) ∧
      Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieOne j : Set X.Lie)) ≤
        (X.map g).lieOne (g.comp j)) ∧
    (IsCompl (X.lieZero j) (X.lieOne j) →
      Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieZero j : Set X.Lie)) =
          (X.map g).lieZero (g.comp j) ∧
        Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieOne j : Set X.Lie)) =
          (X.map g).lieOne (g.comp j)) := by
  refine ⟨⟨span_le_zero j g X, span_le_one j g X⟩, fun hc => ?_⟩
  have hsup := span_sup_span_eq_top j g X hc
  have hinf := lieZero_inf_lieOne_eq_bot (p := p) (g.comp j) (X.map g)
  refine ⟨eq_of_le_of_sup_top_of_inf_bot (span_le_zero j g X) (span_le_one j g X) hsup hinf, ?_⟩
  have hsup' : Submodule.span S ((gv g X) '' (X.lieOne j : Set X.Lie)) ⊔
      Submodule.span S ((gv g X) '' (X.lieZero j : Set X.Lie)) = ⊤ := by rw [sup_comm]; exact hsup
  have hinf' : (X.map g).lieOne (g.comp j) ⊓ (X.map g).lieZero (g.comp j) = ⊥ := by rw [inf_comm]; exact hinf
  exact eq_of_le_of_sup_top_of_inf_bot (span_le_one j g X) (span_le_zero j g X) hsup' hinf'

end S_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image (solution)
