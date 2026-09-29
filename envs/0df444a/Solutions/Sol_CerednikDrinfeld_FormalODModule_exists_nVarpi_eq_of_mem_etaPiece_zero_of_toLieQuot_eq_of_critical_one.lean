-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/75b04eb3-19cb-5632-b93d-e1530e5b12c3

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

noncomputable section

namespace NoncritTransfer

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

end NoncritTransfer

end

open NoncritTransfer MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.GradedCartierModuleData in

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (h1 : ∀ m ∈ X.gradedPiece j 1, ∃ g : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (hL1 : ∀ x y : MvFormalGroup.CartierModule p X.F, x ∈ X.gradedPiece j 1 →
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd x → L x = (X.toGradedCartierModuleData j hc).nMk (y, 0))
    (z : (X.toGradedCartierModuleData j hc).NMod) (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0)
    (htan : ∃ m₁ ∈ X.gradedPiece j 1, (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ (MvFormalGroup.CartierModule.endAct X.varpiEnd m₁)) :
    ∃ z₁ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1, (X.toGradedCartierModuleData j hc).nVarpi z₁ = z := by
  classical
  obtain ⟨S, instS, jS, φ, hφs, hS, Dl, hDl, f, hf, Ll, hLl, hpush⟩ := hL.exists_lift
  obtain ⟨hsemi, hF, hfV, hfPi, hpieces, γl, hγl, hγ⟩ := hf
  have hDV : ∀ m : CartierModule p X.F, (X.toGradedCartierModuleData j hc).verschiebung m = verschiebungInt m := fun _ => rfl
  have hDPi : ∀ m : CartierModule p X.F, (X.toGradedCartierModuleData j hc).varpi m = endAct X.varpiEnd m := fun _ => rfl
  have hDpiece : ∀ (l : Fin 2) (m : CartierModule p X.F), m ∈ (X.toGradedCartierModuleData j hc).piece l ↔ m ∈ X.gradedPiece j (l : ℕ) :=
    fun _ _ => Iff.rfl
  have hVinj : Function.Injective (X.toGradedCartierModuleData j hc).verschiebung := hγ.verschiebung_injective
  have hnv : ∀ m m' : CartierModule p X.F, (X.toGradedCartierModuleData j hc).nVarpi ((X.toGradedCartierModuleData j hc).nMk (m, m')) = (X.toGradedCartierModuleData j hc).nMk ((X.toGradedCartierModuleData j hc).varpi m, (X.toGradedCartierModuleData j hc).varpi m') :=
    fun _ _ => rfl
  obtain ⟨hze, hzn⟩ := AddSubgroup.mem_inf.1 hz
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_nPiece_iff (X.toGradedCartierModuleData j hc) 0 _).1 hzn
  obtain ⟨m₁, hm₁, htq⟩ := htan

  have hta : (X.toGradedCartierModuleData j hc).toLieQuot ((X.toGradedCartierModuleData j hc).nMk (a, b)) = (X.toGradedCartierModuleData j hc).vRange.mkQ a := rfl
  rw [hta, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, (X.toGradedCartierModuleData j hc).mem_vRange_iff] at htq
  obtain ⟨w, hw⟩ := htq
  obtain ⟨g₀, hg₀⟩ : ∃ g : (X.toGradedCartierModuleData j hc).M, (X.toGradedCartierModuleData j hc).verschiebung g = (X.toGradedCartierModuleData j hc).varpi m₁ := h1 m₁ hm₁

  rw [← hDPi] at hw
  have ha' : (X.toGradedCartierModuleData j hc).verschiebung (w + g₀) = a := by
    rw [map_add, hw, hg₀, sub_add_cancel]
  set a' : (X.toGradedCartierModuleData j hc).M := w + g₀ with ha'def
  have ha'0 : a' ∈ (X.toGradedCartierModuleData j hc).piece 1 := by
    apply mem_piece_of_verschiebung_mem (X.toGradedCartierModuleData j hc) hVinj 1
    rw [ha']
    exact ha
  set c := (X.toGradedCartierModuleData j hc).varpi a' + b with hcdef
  have hz0c : (X.toGradedCartierModuleData j hc).nMk (a, b) = (X.toGradedCartierModuleData j hc).nMk (0, c) := by
    have e : ((a, b) : (X.toGradedCartierModuleData j hc).M × (X.toGradedCartierModuleData j hc).M) = ((X.toGradedCartierModuleData j hc).verschiebung a', -(X.toGradedCartierModuleData j hc).varpi a') + (0, c) := by
      rw [Prod.mk_add_mk, add_zero, hcdef, neg_add_cancel_left, ha']
    rw [e, map_add, nMk_verschiebung_neg_varpi, zero_add]
  have hphi : (X.toGradedCartierModuleData j hc).phi L hL.isCartierLMap.map_verschiebung ((X.toGradedCartierModuleData j hc).nMk (a, b)) = (X.toGradedCartierModuleData j hc).nMk (c, 0) := by
    rw [phi_nMk, ← ha', hL.isCartierLMap.map_verschiebung, ← map_add, Prod.mk_add_mk, add_zero]
  have hfix : (X.toGradedCartierModuleData j hc).phi L hL.isCartierLMap.map_verschiebung ((X.toGradedCartierModuleData j hc).nMk (a, b)) = (X.toGradedCartierModuleData j hc).nMk (a, b) :=
    ((X.toGradedCartierModuleData j hc).mem_eta_iff L _ _).1 hze

  have hcc : (X.toGradedCartierModuleData j hc).nMk (c, -c) = 0 := by
    have e : ((c, -c) : (X.toGradedCartierModuleData j hc).M × (X.toGradedCartierModuleData j hc).M) = (c, 0) - (0, c) := by
      rw [Prod.mk_sub_mk, sub_zero, zero_sub]
    rw [e, map_sub, ← hphi, hfix, hz0c, sub_self]
  rw [nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hcc
  obtain ⟨s, hs⟩ := hcc
  rw [nRelMap_apply] at hs
  have hVt : (X.toGradedCartierModuleData j hc).verschiebung ((X.toGradedCartierModuleData j hc).ofSigma s) = c := congrArg Prod.fst hs
  have hPt : (X.toGradedCartierModuleData j hc).varpi ((X.toGradedCartierModuleData j hc).ofSigma s) = c := by
    have h2 := congrArg (fun q => (X.toGradedCartierModuleData j hc).ofSigma q.2) hs
    simp only [ofSigma_toSigma] at h2
    exact neg_inj.1 h2
  set t := (X.toGradedCartierModuleData j hc).ofSigma s with htdef
  have hc1 : c ∈ (X.toGradedCartierModuleData j hc).piece 0 := Submodule.add_mem _ ((X.toGradedCartierModuleData j hc).varpi_mem 1 a' ha'0) hb
  have ht0 : t ∈ (X.toGradedCartierModuleData j hc).piece 1 := by
    apply mem_piece_of_verschiebung_mem (X.toGradedCartierModuleData j hc) hVinj 1
    rw [hVt]
    exact hc1
  have hLt : L t = (X.toGradedCartierModuleData j hc).nMk (t, 0) := hL1 t t ((hDpiece 1 t).1 ht0) (by rw [← hDV, ← hDPi, hVt, hPt])
  refine ⟨(X.toGradedCartierModuleData j hc).nMk (t, 0), AddSubgroup.mem_inf.2 ⟨((X.toGradedCartierModuleData j hc).mem_eta_iff L _ _).2 ?_, nMk_mem_nPiece (X.toGradedCartierModuleData j hc) 1 ht0 (Submodule.zero_mem _)⟩, ?_⟩
  · rw [phi_nMk, hLt, ← map_add, Prod.mk_add_mk, add_zero, add_zero]
  · rw [hnv, map_zero, hPt, ← hphi, hfix]

end S_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one (solution)
