-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0ddd6d2a-1b59-5c7c-9329-6c4abc04f243

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_lambda_injective_of_isHomogeneousVBasis_of_torsionFree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

noncomputable section

namespace LambdaDict

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData

section Datum

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
  (D : GradedCartierModuleData p B j)

theorem exists_eq_teichmuller_smul_add_verschiebung {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    ∃ (c : B) (m : D.M), x = WittVector.teichmuller p c • γ i + D.verschiebung m := by
  classical
  obtain ⟨⟨c, y⟩, hcy, -⟩ := hγ.2 x

  have hsup : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hy : y ∈ D.piece 0 ⊔ D.piece 1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨y0, hy0, y1, hy1, rfl⟩ := Submodule.mem_sup.1 hy

  fin_cases i
  ·
    have hdec : x = (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) +
        (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have hz : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 0 := by
      have : x - (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) ∈ D.piece 0 := Submodule.sub_mem _ hx h0
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ hz h1
    refine ⟨c 0, y1, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl
  · have hdec : x = (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) +
        (WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1) := by
      rw [hcy, Fin.sum_univ_two, map_add]; abel
    have h1 : WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0 ∈ D.piece 1 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 1)) (by simpa using D.verschiebung_mem 0 y0 hy0)
    have h0 : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 0 :=
      Submodule.add_mem _ (Submodule.smul_mem _ _ (hγ.1 0)) (by simpa using D.verschiebung_mem 1 y1 hy1)
    have hz : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 ∈ D.piece 1 := by
      have : x - (WittVector.teichmuller p (c 1) • γ 1 + D.verschiebung y0) ∈ D.piece 1 := Submodule.sub_mem _ hx h1
      rwa [hdec, add_sub_cancel_left] at this
    have hzero : WittVector.teichmuller p (c 0) • γ 0 + D.verschiebung y1 = 0 := by
      have := D.isCompl_piece.disjoint
      rw [Submodule.disjoint_def] at this
      exact this _ h0 hz
    refine ⟨c 1, y0, ?_⟩
    rw [hdec, hzero, add_zero]
    rfl

theorem teichmuller_coeff_unique {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (c c' : Fin 2 → B) (y y' : D.M)
    (h : (∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y =
      (∑ i : Fin 2, WittVector.teichmuller p (c' i) • γ i) + D.verschiebung y') :
    c = c' ∧ y = y' := by
  obtain ⟨cy, -, huniq⟩ := hγ.2 ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y)
  have h1 : (c, y) = cy := huniq (c, y) rfl
  have h2 : (c', y') = cy := huniq (c', y') h
  have := h1.trans h2.symm
  exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩

theorem fin_two_add_one_add_one (l : Fin 2) : l + 1 + 1 = l := by
  fin_cases l <;> rfl

theorem exists_piece_split (l : Fin 2) (g : D.M) :
    ∃ g₁ ∈ D.piece l, ∃ g₂ ∈ D.piece (l + 1), g = g₁ + g₂ := by
  have hsup : D.piece 0 ⊔ D.piece 1 = ⊤ := D.isCompl_piece.sup_eq_top
  have hg : g ∈ D.piece 0 ⊔ D.piece 1 := by rw [hsup]; exact Submodule.mem_top
  obtain ⟨g0, hg0, g1, hg1, rfl⟩ := Submodule.mem_sup.1 hg
  fin_cases l
  · exact ⟨g0, hg0, g1, hg1, rfl⟩
  · exact ⟨g1, hg1, g0, hg0, add_comm _ _⟩

theorem eq_zero_of_mem_piece_of_mem_piece_add_one (l : Fin 2) (m : D.M) (h₁ : m ∈ D.piece l)
    (h₂ : m ∈ D.piece (l + 1)) : m = 0 := by
  have hd := D.isCompl_piece.disjoint
  rw [Submodule.disjoint_def] at hd
  fin_cases l
  · exact hd _ h₁ h₂
  · exact hd _ h₂ h₁

theorem mem_piece_of_verschiebung_mem (hV : Function.Injective D.verschiebung) (l : Fin 2) (g : D.M)
    (hg : D.verschiebung g ∈ D.piece (l + 1)) : g ∈ D.piece l := by
  obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := exists_piece_split D l g
  have h2 : D.verschiebung g₂ ∈ D.piece l := by
    have := D.verschiebung_mem (l + 1) g₂ hg₂
    rwa [fin_two_add_one_add_one] at this
  have h2' : D.verschiebung g₂ ∈ D.piece (l + 1) := by
    have h1 : D.verschiebung g₁ ∈ D.piece (l + 1) := D.verschiebung_mem l g₁ hg₁
    have := Submodule.sub_mem _ hg h1
    rwa [map_add, add_sub_cancel_left] at this
  have hz : D.verschiebung g₂ = 0 := eq_zero_of_mem_piece_of_mem_piece_add_one D l _ h2 h2'
  have : g₂ = 0 := hV (by rw [hz, map_zero])
  rw [this, add_zero]
  exact hg₁

theorem exists_eq_teichmuller_smul_add_verschiebung' {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (i : Fin 2) (x : D.M) (hx : x ∈ D.piece i) :
    ∃ (c : B) (m : D.M), m ∈ D.piece (i + 1) ∧ x = WittVector.teichmuller p c • γ i + D.verschiebung m := by
  obtain ⟨c, m, hxm⟩ := exists_eq_teichmuller_smul_add_verschiebung D hγ i x hx
  refine ⟨c, m, ?_, hxm⟩
  apply mem_piece_of_verschiebung_mem D hγ.verschiebung_injective
  rw [fin_two_add_one_add_one]
  have := Submodule.sub_mem _ hx (Submodule.smul_mem _ (WittVector.teichmuller p c) (hγ.1 i))
  rwa [hxm, add_sub_cancel_left] at this

theorem mem_nPiece_iff (l : Fin 2) (z : D.NMod) :
    z ∈ D.nPiece l ↔ ∃ m m' : D.M, m ∈ D.piece l ∧ m' ∈ D.piece l ∧ D.nMk (m, m') = z := by
  constructor
  · rintro ⟨⟨m, m'⟩, hmm, rfl⟩
    exact ⟨m, m', hmm.1, hmm.2, rfl⟩
  · rintro ⟨m, m', hm, hm', rfl⟩
    exact ⟨(m, m'), ⟨hm, hm'⟩, rfl⟩

theorem nMk_mem_nPiece (l : Fin 2) {m m' : D.M} (hm : m ∈ D.piece l) (hm' : m' ∈ D.piece l) :
    D.nMk (m, m') ∈ D.nPiece l :=
  (mem_nPiece_iff D l _).2 ⟨m, m', hm, hm', rfl⟩

theorem smul_mem_nPiece (l : Fin 2) (w : WittVector p B) {z : D.NMod} (hz : z ∈ D.nPiece l) :
    w • z ∈ D.nPiece l := by
  obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff D l z).1 hz
  rw [smul_nMk]
  exact nMk_mem_nPiece D l (Submodule.smul_mem _ _ hm) (Submodule.smul_mem _ _ hm')

theorem lambda_mem_piece (l : Fin 2) {z : D.NMod} (hz : z ∈ D.nPiece l) : D.lambda z ∈ D.piece (l + 1) := by
  obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff D l z).1 hz
  rw [lambda_nMk]
  exact Submodule.add_mem _ (D.varpi_mem l m hm) (D.verschiebung_mem l m' hm')

theorem apply_basis_mem_nPiece_of_lambda_injective {γ : Fin 2 → D.M} (hγ : D.IsHomogeneousVBasis γ)
    (hlam : Function.Injective D.lambda) (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L) (l : Fin 2) :
    L (γ l) ∈ D.nPiece l := by
  obtain ⟨⟨u, v⟩, huv⟩ := D.nMk_surjective (L (γ l))
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := exists_piece_split D l u
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := exists_piece_split D l v
  have hsplit : D.nMk (u₁ + u₂, v₁ + v₂) = D.nMk (u₁, v₁) + D.nMk (u₂, v₂) := by
    rw [← map_add, Prod.mk_add_mk]
  have ha : D.nMk (u₁, v₁) ∈ D.nPiece l := nMk_mem_nPiece D l hu₁ hv₁
  have hb : D.nMk (u₂, v₂) ∈ D.nPiece (l + 1) := nMk_mem_nPiece D (l + 1) hu₂ hv₂
  have hFl : D.lambda (L (γ l)) ∈ D.piece (l + 1) := by
    rw [hL.lambda_comp]
    exact D.frobenius_mem l _ (hγ.1 l)
  have hb1 : D.lambda (D.nMk (u₂, v₂)) ∈ D.piece l := by
    have := lambda_mem_piece D (l + 1) hb
    rwa [fin_two_add_one_add_one] at this
  have hb2 : D.lambda (D.nMk (u₂, v₂)) ∈ D.piece (l + 1) := by
    have := Submodule.sub_mem _ hFl (lambda_mem_piece D l ha)
    rwa [← huv, hsplit, map_add, add_sub_cancel_left] at this
  have hz : D.lambda (D.nMk (u₂, v₂)) = 0 := eq_zero_of_mem_piece_of_mem_piece_add_one D l _ hb1 hb2
  have : D.nMk (u₂, v₂) = 0 := hlam (by rw [hz, map_zero])
  rw [← huv, hsplit, this, add_zero]
  exact ha

end Datum

section Witt

variable {p : ℕ} [Fact p.Prime]

theorem natCast_eq_verschiebung_one {R : Type} [CommRing R] [CharP R p] :
    ((p : ℕ) : WittVector p R) = WittVector.verschiebung 1 := by
  ext n
  rw [WittVector.coeff_p]
  cases n with
  | zero => rw [WittVector.verschiebung_coeff_zero, if_neg (Nat.zero_ne_one)]
  | succ n =>
    rw [WittVector.verschiebung_coeff_succ]
    cases n with
    | zero => simp
    | succ n => simp

end Witt

end LambdaDict

end

open LambdaDict MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData in

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (n : Fin 2)
    (hinj : ∀ m ∈ X.gradedPiece j (n : ℕ),
      (∃ g : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m) →
        ∃ g' : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g' = m) :
    Set.BijOn (X.toGradedCartierModuleData j hc).lambda
      ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung n : Set _)
      {m : MvFormalGroup.CartierModule p X.F | m ∈ X.gradedPiece j ((n + 1 : Fin 2) : ℕ) ∧
        MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧
        ∃ x ∈ X.gradedPiece j (n : ℕ), ∃ x' : MvFormalGroup.CartierModule p X.F,
          m = MvFormalGroup.CartierModule.endAct X.varpiEnd x + MvFormalGroup.CartierModule.verschiebungInt x'} := by
  classical

  obtain ⟨S, instS, jS, φ, hφs, hS, Dl, hDl, f, hf, Ll, hLl, hpush⟩ := hL.exists_lift
  obtain ⟨hsemi, hF, hfV, hfPi, hpieces, γl, hγl, hγ⟩ := hf
  have hDV : ∀ m : CartierModule p X.F, (X.toGradedCartierModuleData j hc).verschiebung m = verschiebungInt m := fun _ => rfl
  have hDPi : ∀ m : CartierModule p X.F, (X.toGradedCartierModuleData j hc).varpi m = endAct X.varpiEnd m := fun _ => rfl
  have hDpiece : ∀ (l : Fin 2) (m : CartierModule p X.F), m ∈ (X.toGradedCartierModuleData j hc).piece l ↔ m ∈ X.gradedPiece j (l : ℕ) :=
    fun _ _ => Iff.rfl
  have hVinj : Function.Injective (X.toGradedCartierModuleData j hc).verschiebung := hγ.verschiebung_injective

  have hkey : ∀ z : (X.toGradedCartierModuleData j hc).NMod, (X.toGradedCartierModuleData j hc).verschiebung ((X.toGradedCartierModuleData j hc).lambda ((X.toGradedCartierModuleData j hc).phi L hL.isCartierLMap.map_verschiebung z)) =
      (X.toGradedCartierModuleData j hc).varpi ((X.toGradedCartierModuleData j hc).lambda z) := by
    intro z
    obtain ⟨⟨m, m'⟩, rfl⟩ := (X.toGradedCartierModuleData j hc).nMk_surjective z
    have e1 : (X.toGradedCartierModuleData j hc).lambda ((X.toGradedCartierModuleData j hc).phi L hL.isCartierLMap.map_verschiebung ((X.toGradedCartierModuleData j hc).nMk (m, m'))) =
        (X.toGradedCartierModuleData j hc).frobenius m + (X.toGradedCartierModuleData j hc).varpi m' := by
      rw [phi_nMk, map_add, hL.isCartierLMap.lambda_comp, lambda_nMk, map_zero, add_zero]
    rw [e1, lambda_nMk, map_add, map_add, (X.toGradedCartierModuleData j hc).verschiebung_frobenius, ← natCast_eq_verschiebung_one,
      Nat.cast_smul_eq_nsmul, (X.toGradedCartierModuleData j hc).varpi_varpi, (X.toGradedCartierModuleData j hc).varpi_verschiebung]

  have hlaml : Function.Injective Dl.lambda :=
    CerednikDrinfeld.GradedCartierModuleData.lambda_injective_of_isHomogeneousVBasis_of_torsionFree p jS hS Dl γl hγl
  have hLdeg : ∀ (l : Fin 2) (x : CartierModule p X.F), x ∈ (X.toGradedCartierModuleData j hc).piece l → L x ∈ (X.toGradedCartierModuleData j hc).nPiece l := by
    intro l x hx
    obtain ⟨c, x', hx', hxe⟩ := exists_eq_teichmuller_smul_add_verschiebung' (X.toGradedCartierModuleData j hc) hγ l x hx
    rw [hxe, map_add, hL.isCartierLMap.map_smul, hL.isCartierLMap.map_verschiebung]
    refine AddSubgroup.add_mem _ (smul_mem_nPiece (X.toGradedCartierModuleData j hc) l _ ?_) (nMk_mem_nPiece (X.toGradedCartierModuleData j hc) l ?_ (Submodule.zero_mem _))
    ·
      rw [hpush]
      have hup := apply_basis_mem_nPiece_of_lambda_injective Dl hγl hlaml Ll hLl l
      obtain ⟨u, v, hu, hv, huv⟩ := (mem_nPiece_iff Dl l _).1 hup
      rw [← huv, nMap_nMk]
      exact nMk_mem_nPiece (X.toGradedCartierModuleData j hc) l (hpieces l u hu) (hpieces l v hv)
    · have := (X.toGradedCartierModuleData j hc).varpi_mem (l + 1) x' hx'
      rwa [fin_two_add_one_add_one] at this

  have hlaminj : ∀ z ∈ (X.toGradedCartierModuleData j hc).nPiece n, (X.toGradedCartierModuleData j hc).lambda z = 0 → z = 0 := by
    intro z hz h0
    obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff (X.toGradedCartierModuleData j hc) n z).1 hz
    rw [lambda_nMk] at h0
    have hVm : verschiebungInt (-m') = endAct X.varpiEnd m := by
      have h := (eq_neg_of_add_eq_zero_left h0).symm
      rw [← map_neg] at h
      exact h
    obtain ⟨g', hg'⟩ := hinj m ((hDpiece n m).1 hm) ⟨-m', hVm⟩
    have hg'' : (X.toGradedCartierModuleData j hc).verschiebung g' = m := hg'
    have hm' : m' = -(X.toGradedCartierModuleData j hc).varpi g' := by
      apply eq_neg_of_add_eq_zero_right
      apply hVinj
      rw [map_zero, map_add, ← (X.toGradedCartierModuleData j hc).varpi_verschiebung, hg'']
      exact h0
    rw [← hg'', hm', nMk_verschiebung_neg_varpi]
  have hsub : ∀ z₁ ∈ (X.toGradedCartierModuleData j hc).nPiece n, ∀ z₂ ∈ (X.toGradedCartierModuleData j hc).nPiece n, (X.toGradedCartierModuleData j hc).lambda z₁ = (X.toGradedCartierModuleData j hc).lambda z₂ → z₁ = z₂ := by
    intro z₁ h₁ z₂ h₂ h
    have := hlaminj (z₁ - z₂) (AddSubgroup.sub_mem _ h₁ h₂) (by rw [map_sub, h, sub_self])
    exact sub_eq_zero.1 this
  refine ⟨?_, ?_, ?_⟩
  ·
    intro z hz
    obtain ⟨hze, hzn⟩ := AddSubgroup.mem_inf.1 hz
    have hfix : (X.toGradedCartierModuleData j hc).phi L hL.isCartierLMap.map_verschiebung z = z := ((X.toGradedCartierModuleData j hc).mem_eta_iff L _ z).1 hze
    refine ⟨(hDpiece _ _).1 (lambda_mem_piece (X.toGradedCartierModuleData j hc) n hzn), ?_, ?_⟩
    · rw [← hDPi, ← hDV, ← hkey z, hfix]
    · obtain ⟨m, m', hm, hm', rfl⟩ := (mem_nPiece_iff (X.toGradedCartierModuleData j hc) n z).1 hzn
      exact ⟨m, (hDpiece _ _).1 hm, m', by rw [lambda_nMk]; rfl⟩
  ·
    intro z₁ h₁ z₂ h₂ h
    exact hsub z₁ (AddSubgroup.mem_inf.1 h₁).2 z₂ (AddSubgroup.mem_inf.1 h₂).2 h
  ·
    intro m₁ hm₁
    obtain ⟨hm₁p, hm₁i, m, hm, g, hge⟩ := hm₁
    have hm' : m ∈ (X.toGradedCartierModuleData j hc).piece n := (hDpiece _ _).2 hm
    have hg : g ∈ (X.toGradedCartierModuleData j hc).piece n := by
      apply mem_piece_of_verschiebung_mem (X.toGradedCartierModuleData j hc) hVinj
      have hVg : (X.toGradedCartierModuleData j hc).verschiebung g = m₁ - (X.toGradedCartierModuleData j hc).varpi m := by
        rw [hge]; exact (add_sub_cancel_left _ _).symm
      rw [hVg]
      exact Submodule.sub_mem _ ((hDpiece _ _).2 hm₁p) ((X.toGradedCartierModuleData j hc).varpi_mem n m hm')
    set z : (X.toGradedCartierModuleData j hc).NMod := (X.toGradedCartierModuleData j hc).nMk (m, g) with hzdef
    have hzn : z ∈ (X.toGradedCartierModuleData j hc).nPiece n := nMk_mem_nPiece (X.toGradedCartierModuleData j hc) n hm' hg
    have hlamz : (X.toGradedCartierModuleData j hc).lambda z = m₁ := by rw [hzdef, lambda_nMk, hDPi, hDV]; exact hge.symm
    have hphin : (X.toGradedCartierModuleData j hc).phi L hL.isCartierLMap.map_verschiebung z ∈ (X.toGradedCartierModuleData j hc).nPiece n := by
      rw [hzdef, phi_nMk]
      exact AddSubgroup.add_mem _ (hLdeg n m hm') (nMk_mem_nPiece (X.toGradedCartierModuleData j hc) n hg (Submodule.zero_mem _))
    have hfix : (X.toGradedCartierModuleData j hc).phi L hL.isCartierLMap.map_verschiebung z = z := by
      apply hsub _ hphin _ hzn
      apply hVinj
      rw [hkey, hlamz, hDPi, hDV]
      exact hm₁i
    refine ⟨z, AddSubgroup.mem_inf.2 ⟨((X.toGradedCartierModuleData j hc).mem_eta_iff L _ z).2 hfix, hzn⟩, hlamz⟩

end S_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_bijOn_lambda_etaPiece_of_isCanonicalLMap_of_forall_exists_of_charP (solution)
