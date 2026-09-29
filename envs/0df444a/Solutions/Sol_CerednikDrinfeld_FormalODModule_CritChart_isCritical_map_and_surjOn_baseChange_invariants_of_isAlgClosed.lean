-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/dc8b2c20-31eb-5f7a-ae40-81f90462c368

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_field
import Theorems.Thm_CerednikDrinfeld_FormalODModule_existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
import Theorems.Thm_CerednikDrinfeld_FormalODModule_IsSpecial_map
import Theorems.Thm_CerednikDrinfeld_FormalODModule_hasKernelOfDegree_map
import Theorems.Thm_MvFormalGroup_CartierModule_exists_forall_iterate_verschiebung_eq_smul_of_finrank_eq_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

namespace KcEtaConst

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_natCast_of_pow_eq {K : Type u} [Field K] [CharP K p] (x : K) (hx : x ^ p = x) :
    ∃ m : ℕ, x = m := by
  classical
  by_contra hcon
  push Not at hcon
  have hp1 : 1 < p := hp.out.one_lt
  set f : Polynomial K := Polynomial.X ^ p - Polynomial.X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp1
  have hdeg : f.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq K hp1

  set T : Finset K := insert x ((Finset.range p).image (fun m : ℕ => (m : K))) with hT
  have hinj : Set.InjOn (fun m : ℕ => (m : K)) (Finset.range p : Set ℕ) := by
    intro a ha b hb hab
    have hab' : a ≡ b [MOD p] := (CharP.natCast_eq_natCast K p).mp hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rw [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hab'
    exact hab'
  have hcardIm : ((Finset.range p).image (fun m : ℕ => (m : K))).card = p := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hxnot : x ∉ (Finset.range p).image (fun m : ℕ => (m : K)) := by
    intro hxm
    obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hxm
    exact hcon m hm.symm
  have hcardT : T.card = p + 1 := by
    rw [hT, Finset.card_insert_of_notMem hxnot, hcardIm]

  have hroot : ∀ y ∈ T, y ∈ f.roots.toFinset := by
    intro y hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot, hf,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    rw [hT, Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · exact hx
    · obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hy
      have := map_natCast (frobenius K p) m
      rwa [frobenius_def] at this
  have hle : T.card ≤ f.roots.toFinset.card := Finset.card_le_card hroot
  have h2 : f.roots.toFinset.card ≤ p := by
    calc f.roots.toFinset.card ≤ f.roots.card := Multiset.toFinset_card_le _
      _ ≤ f.natDegree := Polynomial.card_roots' f
      _ = p := hdeg
  omega

theorem exists_map_eq_of_frobenius_eq {k K : Type u} [Field k] [CharP k p] [Field K] [CharP K p]
    (g : k →+* K) (w : WittVector p K) (hw : WittVector.frobenius w = w) :
    ∃ u : WittVector p k, WittVector.frobenius u = u ∧ WittVector.map g u = w := by
  classical
  have hcoeff : ∀ n, ∃ m : ℕ, w.coeff n = (m : K) := by
    intro n
    have h := congrArg (fun z : WittVector p K => z.coeff n) hw
    simp only [WittVector.coeff_frobenius_charP] at h
    exact exists_natCast_of_pow_eq (w.coeff n) h
  choose c hc using hcoeff
  refine ⟨WittVector.mk p (fun n => (c n : k)), ?_, ?_⟩
  · ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.coeff_mk]
    have := map_natCast (frobenius k p) (c n)
    rwa [frobenius_def] at this
  · ext n
    rw [WittVector.map_coeff, WittVector.coeff_mk, map_natCast, hc]

section Main

variable {k K : Type u} [Field k] [IsAlgClosed k] [CharP k p] [Field K] [IsAlgClosed K] [CharP K p]

theorem gradedPiece_eq_mod {B : Type u} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (n : ℕ) : X.gradedPiece j n = X.gradedPiece j (n % 2) := by
  conv_lhs => rw [← Nat.mod_add_div n 2]
  exact gradedPiece_add_two_mul X j (n % 2) (n / 2)

theorem gradedPiece_eq_of_mod_eq {B : Type u} [CommRing B] (X : FormalODModule p B)
    (j : Zp2 p →+* B) {m n : ℕ} (h : m % 2 = n % 2) : X.gradedPiece j m = X.gradedPiece j n := by
  rw [gradedPiece_eq_mod X j m, gradedPiece_eq_mod X j n, h]

theorem isCompl_gradedSubmodule_succ {B : Type u} [CommRing B] (X : FormalODModule p B)
    (j : Zp2 p →+* B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (i : ℕ) :
    IsCompl (X.gradedSubmodule j i) (X.gradedSubmodule j (i + 1)) := by
  rw [isCompl_gradedSubmodule_iff]
  rcases Nat.even_or_odd i with ⟨m, hm⟩ | ⟨m, hm⟩
  · have h0 : X.gradedPiece j i = X.gradedPiece j 0 :=
      gradedPiece_eq_of_mod_eq X j (by omega)
    have h1 : X.gradedPiece j (i + 1) = X.gradedPiece j 1 :=
      gradedPiece_eq_of_mod_eq X j (by omega)
    rw [h0, h1]; exact hc
  · have h0 : X.gradedPiece j i = X.gradedPiece j 1 :=
      gradedPiece_eq_of_mod_eq X j (by omega)
    have h1 : X.gradedPiece j (i + 1) = X.gradedPiece j 0 :=
      gradedPiece_eq_of_mod_eq X j (by omega)
    rw [h0, h1]; exact hc.symm

variable (j : Zp2 p →+* k) (X : FormalODModule p k) (g : k →+* K)

noncomputable def bcX : CartierModule p X.F →+ CartierModule p (X.map g).F := baseChange (Φ := X.F) g

theorem bcX_apply (m : CartierModule p X.F) : bcX X g m = baseChange (Φ := X.F) g m := rfl

theorem bcX_verschiebung (m : CartierModule p X.F) :
    bcX X g (verschiebung m) = verschiebung (bcX X g m) :=
  baseChangeEq_verschiebung g rfl m

theorem bcX_pi (m : CartierModule p X.F) :
    bcX X g (endAct X.varpiEnd m) = endAct (X.map g).varpiEnd (bcX X g m) :=
  baseChange_endAct_varpiEnd g X m

theorem bcX_smul (w : WittVector p k) (m : CartierModule p X.F) :
    bcX X g (w • m) = WittVector.map g w • bcX X g m :=
  baseChangeEq_smul_witt g rfl w m

theorem bcX_mem_gradedPiece (n : ℕ) {m : CartierModule p X.F} (hm : m ∈ X.gradedPiece j n) :
    bcX X g m ∈ (X.map g).gradedPiece (g.comp j) n :=
  baseChange_mem_gradedPiece g X j n hm

theorem bcX_mem_invariants (i : ℕ) {m : CartierModule p X.F}
    (hm : m ∈ CritChart.invariants X j i) :
    bcX X g m ∈ CritChart.invariants (X.map g) (g.comp j) i := by
  refine ⟨bcX_mem_gradedPiece j X g i hm.1, ?_⟩
  rw [← bcX_pi, hm.2, bcX_verschiebung]

theorem isHomogeneousVBasis_bcX {γ : Fin 2 → CartierModule p X.F} (hγ : X.IsHomogeneousVBasis j γ) :
    (X.map g).IsHomogeneousVBasis (g.comp j) (fun r => bcX X g (γ r)) :=
  hγ.map g

theorem isCritical_map (hX : X.IsSpecial j) (i : ℕ) (hi : CritChart.IsCritical X j i) :
    CritChart.IsCritical (X.map g) (g.comp j) i := by
  classical
  obtain ⟨γ, hγ⟩ := exists_isHomogeneousVBasis_of_isSpecial_field p j X hX
  have hγ' := isHomogeneousVBasis_bcX j X g hγ
  have hX' : (X.map g).IsSpecial (g.comp j) := IsSpecial.map j g X hX
  intro m' hm'
  obtain ⟨⟨a, y⟩, hy, hEq⟩ :=
    (existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece p (g.comp j) (X.map g)
      hX'.1 (fun r => bcX X g (γ r)) hγ' i 1 m' hm').exists
  rw [Fin.sum_univ_one] at hEq
  simp only [Fin.val_zero, Function.iterate_zero, id_eq, Function.iterate_one] at hEq
  have hγi : γ ⟨(i + 0) % 2, Nat.mod_lt _ two_pos⟩ ∈ X.gradedPiece j i := by
    have h := hγ.1 (⟨(i + 0) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2)
    rw [gradedPiece_eq_of_mod_eq X j (show ((i + 0) % 2) % 2 = i % 2 by omega)] at h
    exact h
  obtain ⟨g₀, hg₀⟩ := hi _ hγi
  refine ⟨homothety (a 0 ^ p) (bcX X g g₀) + endAct (X.map g).varpiEnd y, ?_⟩
  have h1 : endAct (X.map g).varpiEnd (bcX X g (γ ⟨(i + 0) % 2, Nat.mod_lt _ two_pos⟩)) =
      verschiebung (bcX X g g₀) := by
    rw [← bcX_pi, ← hg₀, bcX_verschiebung]
  rw [hEq, map_add, map_add, endAct_homothety, h1, homothety_verschiebung, endAct_verschiebung]

theorem hasHeight_map (hX4 : X.HasHeight 4) : (X.map g).HasHeight 4 := by
  have h := hasKernelOfDegree_map g (X.act (p : Zp2 p)) (fun i => (X.isLawHom_act _).1 i) hX4
  exact h

theorem exists_iterate_verschiebung_eq_smul (hX4 : X.HasHeight 4) :
    ∃ N : ℕ, ∀ f : CartierModule p (X.map g).F, ∃ f' : CartierModule p (X.map g).F,
      (⇑(verschiebung (p := p) (Φ := (X.map g).F)))^[N] f = (p : WittVector p K) • f' := by
  have h4 := hasHeight_map X g hX4
  have hK := h4.2.2 K (RingHom.id K)
  rw [SpecialFormal.Series.map_ringHom_id, act_natCast] at hK
  exact MvFormalGroup.CartierModule.exists_forall_iterate_verschiebung_eq_smul_of_finrank_eq_pow p
    (X.map g).F 4 hK

theorem lang_basis {k₁ : Type u} [Field k₁] [IsAlgClosed k₁] [CharP k₁ p] (j₁ : Zp2 p →+* k₁)
    (Y : FormalODModule p k₁) (hY : Y.IsSpecial j₁) (hY4 : Y.HasHeight 4) (i : ℕ)
    (hi : CritChart.IsCritical Y j₁ i) :
    ∃ e : Fin 2 → CartierModule p Y.F,
      (∀ r, e r ∈ CritChart.invariants Y j₁ i) ∧
      (∀ m ∈ Y.gradedPiece j₁ i, ∃! w : Fin 2 → WittVector p k₁, m = ∑ r, w r • e r) ∧
      (∀ w : Fin 2 → WittVector p k₁,
        (∑ r, w r • e r) ∈ CritChart.invariants Y j₁ i ↔ ∀ r, WittVector.frobenius (w r) = w r) := by
  obtain ⟨e, h1, h2, h3, -, -⟩ :=
    SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
      p j₁ ⟨Y, hY, hY4⟩ i hi
  exact ⟨e, h1, h2, h3⟩

theorem main (hX : X.IsSpecial j) (hX4 : X.HasHeight 4) (i : ℕ) (hi : CritChart.IsCritical X j i) :
    CritChart.IsCritical (X.map g) (g.comp j) i ∧
    (∀ m ∈ CritChart.invariants X j i, bcX X g m ∈ CritChart.invariants (X.map g) (g.comp j) i) ∧
    (∀ m' ∈ CritChart.invariants (X.map g) (g.comp j) i,
      ∃ m ∈ CritChart.invariants X j i, bcX X g m = m') := by
  classical
  have hcrit' := isCritical_map j X g hX i hi
  refine ⟨hcrit', fun m hm => bcX_mem_invariants j X g i hm, ?_⟩
  have hX' : (X.map g).IsSpecial (g.comp j) := IsSpecial.map j g X hX
  have hX4' : (X.map g).HasHeight 4 := hasHeight_map X g hX4

  obtain ⟨e, he_inv, he_basis, he_char⟩ := lang_basis j X hX hX4 i hi
  obtain ⟨e', he'_inv, he'_basis, -⟩ := lang_basis (g.comp j) (X.map g) hX' hX4' i hcrit'

  obtain ⟨γ, hγ⟩ := exists_isHomogeneousVBasis_of_isSpecial_field p j X hX
  have hγ' := isHomogeneousVBasis_bcX j X g hγ

  have hgr := isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne p j X hX.1
  have hgr' := isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne p (g.comp j) (X.map g) hX'.1

  obtain ⟨S, hS⟩ : ∃ S : Submodule (WittVector p K) (CartierModule p (X.map g).F),
      S = Submodule.span (WittVector p K) (Set.range fun r => bcX X g (e r)) := ⟨_, rfl⟩
  obtain ⟨Mi, hMi⟩ : ∃ Mi : Submodule (WittVector p K) (CartierModule p (X.map g).F),
      Mi = (X.map g).gradedSubmodule (g.comp j) i := ⟨_, rfl⟩
  have hmemMi : ∀ m, m ∈ Mi ↔ m ∈ (X.map g).gradedPiece (g.comp j) i := by
    intro m; rw [hMi]; exact Iff.rfl
  have hbc_e_mem : ∀ r, bcX X g (e r) ∈ (X.map g).gradedPiece (g.comp j) i := fun r =>
    bcX_mem_gradedPiece j X g i (he_inv r).1
  have hbc_e_S : ∀ r, bcX X g (e r) ∈ S := fun r => by
    rw [hS]; exact Submodule.subset_span ⟨r, rfl⟩
  have hS_le : S ≤ Mi := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact (hmemMi _).2 (hbc_e_mem r)

  have hbcMi : ∀ x ∈ X.gradedPiece j i, bcX X g x ∈ S := by
    intro x hx
    obtain ⟨w, hw, -⟩ := he_basis x hx
    rw [hw, map_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [bcX_smul]
    exact Submodule.smul_mem _ _ (hbc_e_S r)

  have hVn : ∀ (n l : ℕ) (w : WittVector p K) (x : CartierModule p X.F),
      x ∈ X.gradedPiece j l → (l + n) % 2 = i % 2 →
      (⇑(verschiebung (p := p) (Φ := (X.map g).F)))^[n] (w • bcX X g x) ∈ S := by
    intro n
    induction n with
    | zero =>
      intro l w x hx hln
      rw [Function.iterate_zero, id_eq]
      have hx' : x ∈ X.gradedPiece j i := by
        rw [gradedPiece_eq_of_mod_eq X j (show i % 2 = l % 2 by omega)]; exact hx
      exact Submodule.smul_mem _ _ (hbcMi x hx')
    | succ n ih =>
      intro l w x hx hln
      rw [Function.iterate_succ_apply, verschiebung_smul, ← bcX_verschiebung]
      refine ih (l + 1) _ (verschiebung x) ?_ (by omega)
      exact (hgr.2.1 l x).2 hx

  obtain ⟨N₀, hN₀⟩ := exists_iterate_verschiebung_eq_smul X g hX4
  have hcS : IsCompl Mi ((X.map g).gradedSubmodule (g.comp j) (i + 1)) := by
    rw [hMi]; exact isCompl_gradedSubmodule_succ (X.map g) (g.comp j) hgr'.1 i
  have hMi_le : Mi ≤ S ⊔ (Ideal.span {(p : WittVector p K)}) • Mi := by
    intro m' hm'
    have hm'gp : m' ∈ (X.map g).gradedPiece (g.comp j) i := (hmemMi _).1 hm'
    obtain ⟨⟨a, y⟩, hy, hEq⟩ :=
      (existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece p (g.comp j) (X.map g)
        hX'.1 _ hγ' i N₀ m' hm'gp).exists

    have hfin : (∑ r : Fin N₀, (⇑(verschiebung (p := p) (Φ := (X.map g).F)))^[(r : ℕ)]
        (homothety (a r) (bcX X g (γ ⟨(i + r) % 2, Nat.mod_lt _ two_pos⟩)))) ∈ S := by
      refine Submodule.sum_mem _ fun r _ => ?_
      rw [← teichmuller_smul]
      have hγr := hγ.1 (⟨(i + r) % 2, Nat.mod_lt _ two_pos⟩ : Fin 2)
      exact hVn r ((i + r) % 2) _ (γ ⟨(i + r) % 2, Nat.mod_lt _ two_pos⟩) hγr (by omega)

    obtain ⟨f', hf'⟩ := hN₀ y
    have htop : f' ∈ Mi ⊔ (X.map g).gradedSubmodule (g.comp j) (i + 1) := by
      rw [hcS.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨fi, hfi, fj, hfj, hff⟩ := Submodule.mem_sup.mp htop

    have hpfj_i : (p : WittVector p K) • fj ∈ Mi := by
      have h1 : m' - (∑ r : Fin N₀, (⇑(verschiebung (p := p) (Φ := (X.map g).F)))^[(r : ℕ)]
          (homothety (a r) (bcX X g (γ ⟨(i + r) % 2, Nat.mod_lt _ two_pos⟩)))) -
          (p : WittVector p K) • fi = (p : WittVector p K) • fj := by
        rw [hEq, hf', ← hff, smul_add]; abel
      rw [← h1]
      exact Mi.sub_mem (Mi.sub_mem hm' (hS_le hfin)) (Mi.smul_mem _ hfi)
    have hpfj_j : (p : WittVector p K) • fj ∈ (X.map g).gradedSubmodule (g.comp j) (i + 1) :=
      Submodule.smul_mem _ _ hfj
    have hpfj : (p : WittVector p K) • fj = 0 := by
      have := hcS.disjoint.le_bot (Submodule.mem_inf.mpr ⟨hpfj_i, hpfj_j⟩)
      simp at this
      exact this
    have hm'eq : m' = (∑ r : Fin N₀, (⇑(verschiebung (p := p) (Φ := (X.map g).F)))^[(r : ℕ)]
        (homothety (a r) (bcX X g (γ ⟨(i + r) % 2, Nat.mod_lt _ two_pos⟩)))) +
        (p : WittVector p K) • fi := by
      rw [hEq, hf', ← hff, smul_add, hpfj, add_zero]
    rw [hm'eq]
    exact Submodule.add_mem_sup hfin
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hfi)

  have hMi_span : Mi = Submodule.span (WittVector p K) (Set.range e') := by
    apply le_antisymm
    · intro m hm
      obtain ⟨w, hw, -⟩ := he'_basis m ((hmemMi _).1 hm)
      rw [hw]
      exact Submodule.sum_mem _ fun r _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨r, rfl⟩
      exact (hmemMi _).2 (he'_inv r).1
  have hMi_fg : Mi.FG := by
    rw [hMi_span]; exact Submodule.fg_span (Set.finite_range e')
  have hI : Ideal.span {(p : WittVector p K)} ≤ (⊥ : Ideal (WittVector p K)).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (WittVector.irreducible p).not_isUnit
  have hMi_S : Mi ≤ S := Submodule.le_of_le_smul_of_le_jacobson_bot hMi_fg hI hMi_le

  haveI : Module.Finite (WittVector p K) Mi := Module.Finite.iff_fg.mpr hMi_fg
  have he'_Mi : ∀ r, e' r ∈ Mi := fun r => (hmemMi _).2 (he'_inv r).1
  have hbce_Mi : ∀ r, bcX X g (e r) ∈ Mi := fun r => (hmemMi _).2 (hbc_e_mem r)
  obtain ⟨T, hT⟩ : ∃ T : (Fin 2 → WittVector p K) →ₗ[WittVector p K] Mi,
      T = ∑ r : Fin 2, (LinearMap.proj r).smulRight (⟨bcX X g (e r), hbce_Mi r⟩ : Mi) := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ E' : (Fin 2 → WittVector p K) →ₗ[WittVector p K] Mi,
      E' = ∑ r : Fin 2, (LinearMap.proj r).smulRight (⟨e' r, he'_Mi r⟩ : Mi) := ⟨_, rfl⟩
  have hT_apply : ∀ w, ((T w : Mi) : CartierModule p (X.map g).F) = ∑ r, w r • bcX X g (e r) := by
    intro w
    rw [hT]
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have hE'_apply : ∀ w, ((E' w : Mi) : CartierModule p (X.map g).F) = ∑ r, w r • e' r := by
    intro w
    rw [hE']
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Submodule.coe_sum, Submodule.coe_smul]
  have hE'_inj : Function.Injective E' := by
    intro w₁ w₂ h
    have h' : (∑ r, w₁ r • e' r) = ∑ r, w₂ r • e' r := by
      rw [← hE'_apply, ← hE'_apply, h]
    have hmem : (∑ r, w₁ r • e' r) ∈ (X.map g).gradedPiece (g.comp j) i := by
      rw [← hE'_apply]; exact (hmemMi _).1 (E' w₁).2
    obtain ⟨w, hw, huniq⟩ := he'_basis _ hmem
    exact (huniq w₁ rfl).trans (huniq w₂ h').symm
  have hT_surj : Function.Surjective T := by
    intro m
    have hm : (m : CartierModule p (X.map g).F) ∈ S := hMi_S m.2
    rw [hS, Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨c, Subtype.ext ?_⟩
    rw [hT_apply, hc]
  have hT_inj : Function.Injective T :=
    OrzechProperty.injective_of_surjective_of_injective E' T hE'_inj hT_surj

  intro m' hm'
  obtain ⟨w, hw⟩ := hT_surj ⟨m', (hmemMi _).2 hm'.1⟩
  have hm'eq : m' = ∑ r, w r • bcX X g (e r) := by
    rw [← hT_apply, hw]

  have hbc_inv : ∀ r, bcX X g (e r) ∈ CritChart.invariants (X.map g) (g.comp j) i := fun r =>
    bcX_mem_invariants j X g i (he_inv r)
  have hPi : endAct (X.map g).varpiEnd m' =
      verschiebung (∑ r, WittVector.frobenius (w r) • bcX X g (e r)) := by
    rw [hm'eq, map_sum, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [endAct_smul_witt, (hbc_inv r).2, smul_verschiebung]
  have hV : endAct (X.map g).varpiEnd m' = verschiebung (∑ r, w r • bcX X g (e r)) := by
    rw [hm'.2, hm'eq]
  have hfix : (fun r => WittVector.frobenius (w r)) = w := by
    have h1 : (∑ r, WittVector.frobenius (w r) • bcX X g (e r)) = ∑ r, w r • bcX X g (e r) :=
      verschiebung_injective (hPi.symm.trans hV)
    apply hT_inj
    apply Subtype.ext
    rw [hT_apply, hT_apply]
    exact h1

  have hu : ∀ r, ∃ u : WittVector p k, WittVector.frobenius u = u ∧ WittVector.map g u = w r :=
    fun r => exists_map_eq_of_frobenius_eq g (w r) (congrFun hfix r)
  choose u hu_frob hu_map using hu
  refine ⟨∑ r, u r • e r, (he_char u).2 hu_frob, ?_⟩
  rw [hm'eq, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [bcX_smul, hu_map]

end Main

end KcEtaConst

theorem solution
    (p : ℕ) [Fact p.Prime] {k K : Type u} [Field k] [IsAlgClosed k] [CharP k p]
    [Field K] [IsAlgClosed K] [CharP K p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (X : CerednikDrinfeld.FormalODModule p k)
    (hX : X.IsSpecial j) (hX4 : X.HasHeight 4) (g : k →+* K) (i : ℕ)
    (hi : CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j i) :
    CerednikDrinfeld.FormalODModule.CritChart.IsCritical (X.map g) (g.comp j) i ∧
    (∀ m ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants X j i,
      MvFormalGroup.CartierModule.baseChange (Φ := X.F) g m ∈
        CerednikDrinfeld.FormalODModule.CritChart.invariants (X.map g) (g.comp j) i) ∧
    (∀ m' ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants (X.map g) (g.comp j) i,
      ∃ m ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants X j i,
        MvFormalGroup.CartierModule.baseChange (Φ := X.F) g m = m') :=
  KcEtaConst.main j X g hX hX4 i hi

end S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed (solution)
