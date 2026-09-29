-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/05089ff5-a761-5fe2-8259-da97e7952781

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
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

universe u

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

namespace ConstantsExistSol

variable {p : ℕ} [hp : Fact p.Prime]

noncomputable def padicToZp2 : ℤ_[p] →+* Zp2 p :=
  (WittVector.map (algebraMap (ZMod p) (GaloisField p 2))).comp (WittVector.equiv p).symm.toRingHom

section Generic
variable {d : ℕ} {R : Type u} [CommRing R] {Φ : MvFormalGroup d R} [Φ.IsComm]

local notation "V" => (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ))

theorem iterateV_add (m : ℕ) (f g : CartierModule p Φ) : (⇑V)^[m] (f + g) = (⇑V)^[m] f + (⇑V)^[m] g := by
  induction m generalizing f g with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_add]

theorem iterateV_zero (m : ℕ) : (⇑V)^[m] (0 : CartierModule p Φ) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]

theorem iterateV_sum {ι : Type} (s : Finset ι) (m : ℕ) (f : ι → CartierModule p Φ) :
    (⇑V)^[m] (∑ x ∈ s, f x) = ∑ x ∈ s, (⇑V)^[m] (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [iterateV_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, iterateV_add, ih]

theorem iterateV_add_apply (m n : ℕ) (f : CartierModule p Φ) : (⇑V)^[m + n] f = (⇑V)^[m] ((⇑V)^[n] f) := by
  rw [Function.iterate_add_apply]

theorem endAct_iterateV (φ : MvFormalGroup.End Φ) (m : ℕ) (f : CartierModule p Φ) :
    endAct φ ((⇑V)^[m] f) = (⇑V)^[m] (endAct φ f) := by
  induction m generalizing f with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', endAct_verschiebungInt, ih]

theorem homothety_iterateV (μ : R) (m : ℕ) (f : CartierModule p Φ) :
    homothety μ ((⇑V)^[m] f) = (⇑V)^[m] (homothety (μ ^ p ^ m) f) := by
  induction m generalizing μ f with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, homothety_verschiebungInt, ← pow_mul,
      ← pow_succ]

noncomputable def expand (f : Fin d → CartierModule p Φ) (N : ℕ) (ch : Fin N → Fin d → R) : CartierModule p Φ :=
  ∑ m : Fin N, (⇑V)^[(m : ℕ)] (∑ i : Fin d, homothety (ch m i) (f i))

theorem expand_def (f : Fin d → CartierModule p Φ) (N : ℕ) (ch : Fin N → Fin d → R) :
    expand f N ch = ∑ m : Fin N, (⇑V)^[(m : ℕ)] (∑ i : Fin d, homothety (ch m i) (f i)) := rfl

theorem endAct_expand (φ : MvFormalGroup.End Φ) (f : Fin d → CartierModule p Φ) (lam : Fin d → R)
    (hφ : ∀ k, endAct φ (f k) = homothety (lam k) (f k)) (N : ℕ) (ch : Fin N → Fin d → R) :
    endAct φ (expand f N ch) = expand f N (fun m k => ch m k * lam k) := by
  simp only [expand_def, map_sum, endAct_iterateV, endAct_homothety, hφ, ← homothety_mul]

theorem homothety_expand (μ : R) (f : Fin d → CartierModule p Φ) (N : ℕ) (ch : Fin N → Fin d → R) :
    homothety μ (expand f N ch) = expand f N (fun m k => μ ^ p ^ (m : ℕ) * ch m k) := by
  simp only [expand_def, map_sum, homothety_iterateV, ← homothety_mul]

theorem expand_snoc (f : Fin d → CartierModule p Φ) (N : ℕ) (ch : Fin N → Fin d → R) (c : Fin d → R) :
    expand f (N + 1) (Fin.snoc ch c) = expand f N ch + (⇑V)^[N] (∑ i : Fin d, homothety (c i) (f i)) := by
  rw [expand_def, Fin.sum_univ_castSucc, expand_def]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]

end Generic

end ConstantsExistSol

namespace ConstantsExistSol

section OD
variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

theorem exists_pow_p_ne : ∃ c : GaloisField p 2, c ^ p ≠ c := by
  classical
  letI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  by_contra h
  push_neg at h
  have h1 : 1 < p := hp.out.one_lt
  have hP0 : (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero (GaloisField p 2) h1
  have hdeg : (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).natDegree = p :=
    FiniteField.X_pow_card_sub_X_natDegree_eq (GaloisField p 2) h1
  have hroots : ∀ c : GaloisField p 2, c ∈ (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).roots :=
    fun c => (Polynomial.mem_roots hP0).mpr (by simp [Polynomial.IsRoot, h c])
  have hcard : Fintype.card (GaloisField p 2) ≤ p := by
    calc Fintype.card (GaloisField p 2) = (Finset.univ : Finset (GaloisField p 2)).card := Finset.card_univ.symm
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).roots.toFinset.card :=
          Finset.card_le_card (fun c _ => Multiset.mem_toFinset.mpr (hroots c))
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).roots.card := Multiset.toFinset_card_le _
      _ ≤ (Polynomial.X ^ p - Polynomial.X : Polynomial (GaloisField p 2)).natDegree := Polynomial.card_roots' _
      _ = p := hdeg
  have hc2 : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p 2 two_ne_zero]
  rw [hc2, pow_two] at hcard
  exact absurd hcard (by nlinarith)

theorem actEnd_teichmuller_mul_varpiEnd (X : FormalODModule p B) (c : GaloisField p 2) :
    X.actEnd (WittVector.teichmuller p c) * X.varpiEnd = X.varpiEnd * X.actEnd (WittVector.teichmuller p (c ^ p)) := by
  rw [FormalODModule.varpiEnd_mul_actEnd, WittVector.frobenius_teichmuller_eq, ← pow_mul, ← pow_two,
    FormalODModule.pow_card_galoisField]

theorem endAct_actEnd_varpi (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (f : CartierModule p X.F) (hf : f ∈ X.gradedPiece j n) (c : GaloisField p 2) :
    endAct (X.actEnd (WittVector.teichmuller p c)) (endAct X.varpiEnd f) =
      homothety (j (WittVector.teichmuller p c) ^ p ^ (n + 1)) (endAct X.varpiEnd f) := by
  have h := congrArg (fun φ => endAct φ f) (actEnd_teichmuller_mul_varpiEnd X c)
  simp only [map_mul, AddMonoid.End.coe_mul, Function.comp_apply] at h
  rw [h, (FormalODModule.mem_gradedPiece_iff X j n f).mp hf (c ^ p), endAct_homothety, map_pow (WittVector.teichmuller p),
    map_pow j, ← pow_mul, ← pow_succ']

theorem pow_teich_mod_two (j : Zp2 p →+* B) (c : GaloisField p 2) (a : ℕ) :
    j (WittVector.teichmuller p c) ^ p ^ a = j (WittVector.teichmuller p c) ^ p ^ (a % 2) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rcases Nat.lt_or_ge a 2 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [add_comm, FormalODModule.apply_teichmuller_pow_pow_add_two, ih b (by omega), Nat.add_mod_right]

theorem isUnit_sub (j : Zp2 p →+* B) (c : GaloisField p 2) (hc : c ^ p ≠ c) :
    IsUnit (j (WittVector.teichmuller p c) - j (WittVector.teichmuller p c) ^ p) := by
  rw [← map_pow, ← map_sub]
  apply IsUnit.map
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [← map_pow (WittVector.teichmuller p), ← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
    WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  exact sub_ne_zero.mpr (Ne.symm hc)

end OD

end ConstantsExistSol

namespace ConstantsExistSol
section Aux
variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R] {Φ : MvFormalGroup d R} [Φ.IsComm]

theorem sum_homothety_ite (f : Fin d → CartierModule p Φ) (k₀ : Fin d) (a : R) :
    (∑ k : Fin d, homothety (if k = k₀ then a else 0) (f k)) = homothety a (f k₀) := by
  classical
  rw [Finset.sum_eq_single k₀]
  · rw [if_pos rfl]
  · intro k _ hk
    rw [if_neg hk, homothety_zero_left]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Aux
end ConstantsExistSol

open ConstantsExistSol in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ) :
    ∃ a : ℕ → Fin 2 → B, X.HasStructureConstants γ a ∧ a 0 0 * a 0 1 = (p : B) := by
  classical
  letI : Algebra ℤ_[p] B := (j.comp padicToZp2).toAlgebra
  have hexp := fun (i : Fin 2) (N : ℕ) =>
    MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add p X.F γ hγ.2
      (endAct X.varpiEnd (γ i)) N

  have hexp1 := fun (g : CartierModule p X.F) =>
    MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add p X.F γ hγ.2 g 1

  have parity : ∀ (i : Fin 2) (N : ℕ) (ch : Fin N → Fin 2 → B) (r : CartierModule p X.F),
      endAct X.varpiEnd (γ i) = expand γ N ch + (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] r →
      ∀ (m : Fin N) (k : Fin 2), (k : ℕ) % 2 ≠ ((m : ℕ) + i + 1) % 2 → ch m k = 0 := by
    intro i N ch r hE m k hpar
    obtain ⟨c, hc⟩ := exists_pow_p_ne (p := p)
    set lam : B := j (WittVector.teichmuller p c) with hlam
    have hγk : ∀ k : Fin 2, endAct (X.actEnd (WittVector.teichmuller p c)) (γ k) = homothety (lam ^ p ^ (k : ℕ)) (γ k) :=
      fun k => (FormalODModule.mem_gradedPiece_iff X j k (γ k)).mp (hγ.1 k) c
    have E1 : endAct (X.actEnd (WittVector.teichmuller p c)) (endAct X.varpiEnd (γ i)) =
        expand γ N (fun m k => ch m k * lam ^ p ^ (k : ℕ)) +
          (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] (endAct (X.actEnd (WittVector.teichmuller p c)) r) := by
      rw [hE, map_add, endAct_expand _ γ (fun k => lam ^ p ^ (k : ℕ)) hγk, endAct_iterateV]
    have E2 : endAct (X.actEnd (WittVector.teichmuller p c)) (endAct X.varpiEnd (γ i)) =
        expand γ N (fun m k => (lam ^ p ^ ((i : ℕ) + 1)) ^ p ^ (m : ℕ) * ch m k) +
          (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] (homothety ((lam ^ p ^ ((i : ℕ) + 1)) ^ p ^ N) r) := by
      rw [endAct_actEnd_varpi X j i (γ i) (hγ.1 i) c, hE, map_add, homothety_expand, homothety_iterateV]

    obtain ⟨chr, -, huniq⟩ :=
      MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add p X.F γ hγ.2
        (endAct (X.actEnd (WittVector.teichmuller p c)) (endAct X.varpiEnd (γ i))) N
    have u1 := huniq ⟨fun m k => ch m k * lam ^ p ^ (k : ℕ), endAct (X.actEnd (WittVector.teichmuller p c)) r⟩ E1
    have u2 := huniq ⟨fun m k => (lam ^ p ^ ((i : ℕ) + 1)) ^ p ^ (m : ℕ) * ch m k,
      homothety ((lam ^ p ^ ((i : ℕ) + 1)) ^ p ^ N) r⟩ E2
    have hmk : ch m k * lam ^ p ^ (k : ℕ) = (lam ^ p ^ ((i : ℕ) + 1)) ^ p ^ (m : ℕ) * ch m k := by
      have h := congrArg Prod.fst (u1.trans u2.symm)
      exact congrFun (congrFun h m) k
    rw [← pow_mul, ← pow_add, pow_teich_mod_two j c (k : ℕ), pow_teich_mod_two j c ((i : ℕ) + 1 + (m : ℕ)),
      mul_comm _ (ch m k)] at hmk
    have hidx : ((i : ℕ) + 1 + (m : ℕ)) % 2 = ((m : ℕ) + i + 1) % 2 := by congr 1; ring
    rw [hidx] at hmk

    have hu := isUnit_sub j c hc
    rcases Nat.mod_two_eq_zero_or_one (k : ℕ) with hk0 | hk1 <;>
      rcases Nat.mod_two_eq_zero_or_one ((m : ℕ) + i + 1) with hm0 | hm1
    · exact absurd (hk0.trans hm0.symm) hpar
    · rw [hk0, hm1, pow_zero, pow_one, pow_one] at hmk
      have : ch m k * (lam - lam ^ p) = 0 := by rw [mul_sub, hmk, sub_self]
      exact (hu.mul_left_eq_zero.mp this)
    · rw [hk1, hm0, pow_zero, pow_one, pow_one] at hmk
      have : ch m k * (lam - lam ^ p) = 0 := by rw [mul_sub, ← hmk, sub_self]
      exact (hu.mul_left_eq_zero.mp this)
    · exact absurd (hk1.trans hm1.symm) hpar

  have hexE : ∀ (i : Fin 2) (N : ℕ), ∃ chr : (Fin N → Fin 2 → B) × CartierModule p X.F,
      endAct X.varpiEnd (γ i) = expand γ N chr.1 + (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] chr.2 ∧
      ∀ y : (Fin N → Fin 2 → B) × CartierModule p X.F,
        endAct X.varpiEnd (γ i) = expand γ N y.1 + (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] y.2 → y = chr :=
    fun i N => hexp i N
  choose dig hdig huq using hexE
  let a : ℕ → Fin 2 → B := fun m i => (dig i (m + 1)).1 (Fin.last m) (piIndex m i)

  have H : ∀ (i : Fin 2) (N : ℕ), ∃ h : CartierModule p X.F,
      endAct X.varpiEnd (γ i) =
        (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)] (homothety (a m i) (γ (piIndex m i)))) +
          (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N] h := by
    intro i N
    induction N with
    | zero => exact ⟨endAct X.varpiEnd (γ i), by simp⟩
    | succ N ih =>
      obtain ⟨hN, hEq⟩ := ih

      obtain ⟨⟨c, h'⟩, hc, -⟩ := hexp1 hN
      simp only [Fin.sum_univ_one, Fin.val_zero, Function.iterate_zero, Function.iterate_one, id_eq] at hc

      let dN : Fin N → Fin 2 → B := fun m k => if k = piIndex m i then a m i else 0
      have hS : (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)] (homothety (a m i) (γ (piIndex m i)))) =
          expand γ N dN := by
        simp only [expand_def, dN, sum_homothety_ite]

      have hE' : endAct X.varpiEnd (γ i) = expand γ (N + 1) (Fin.snoc dN (c 0)) +
          (⇑(verschiebungInt (p := p) (Φ := X.F)))^[N + 1] h' := by
        rw [hEq, hc, expand_snoc, hS, iterateV_add, Function.iterate_succ_apply, add_assoc]

      have hy := huq i (N + 1) ⟨Fin.snoc dN (c 0), h'⟩ hE'
      have hcd : c 0 = (dig i (N + 1)).1 (Fin.last N) := by
        have h := congrArg Prod.fst hy
        simp only at h
        rw [← h, Fin.snoc_last]

      have hpar := parity i (N + 1) (dig i (N + 1)).1 (dig i (N + 1)).2 (hdig i (N + 1)) (Fin.last N)
      have hck : ∀ k : Fin 2, c 0 k = if k = piIndex N i then a N i else 0 := by
        intro k
        by_cases hk : k = piIndex N i
        · rw [if_pos hk, hcd, hk]
        · rw [if_neg hk, hcd]
          apply hpar k
          intro hmod
          apply hk
          simp only [Fin.val_last] at hmod
          ext
          rw [piIndex_val, ← hmod]
          exact (Nat.mod_eq_of_lt k.2).symm
      have hsum : (∑ k : Fin 2, homothety (c 0 k) (γ k)) = homothety (a N i) (γ (piIndex N i)) := by
        simp only [hck, sum_homothety_ite]
      refine ⟨h', ?_⟩
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [hEq, hc, hsum, iterateV_add, Function.iterate_succ_apply, add_assoc]

  have hprod : a 0 0 * a 0 1 = (p : B) := by
    obtain ⟨h0, e0⟩ := H 0 1
    obtain ⟨h1, e1⟩ := H 1 1
    simp only [Fin.sum_univ_one, Fin.val_zero, Function.iterate_zero, Function.iterate_one, id_eq] at e0 e1
    have hpi0 : piIndex 0 (0 : Fin 2) = 1 := by ext; simp [piIndex_val]
    have hpi1 : piIndex 0 (1 : Fin 2) = 0 := by ext; simp [piIndex_val]
    rw [hpi0] at e0
    rw [hpi1] at e1

    have hPP : ∀ f : CartierModule p X.F, endAct X.varpiEnd (endAct X.varpiEnd f) = p • f := by
      intro f
      have h := congrArg (fun φ => endAct φ f) (FormalODModule.varpiEnd_mul_varpiEnd X)
      simp only [map_mul, AddMonoid.End.coe_mul, Function.comp_apply] at h
      rw [h, map_natCast, endAct_natCast]

    have key : ∀ (i : Fin 2), (a 0 0 * a 0 1 - (p : B)) • tangent (γ i) = 0 := by
      intro i
      fin_cases i
      · show (a 0 0 * a 0 1 - (p : B)) • tangent (γ 0) = 0
        have t1 := congrArg tangent (hPP (γ 0))
        rw [e0, map_add, endAct_homothety, endAct_verschiebungInt, e1] at t1
        simp only [map_add, tangent_homothety, tangent_verschiebungInt, smul_zero, add_zero, smul_smul, map_nsmul] at t1
        rw [sub_smul, t1, Nat.cast_smul_eq_nsmul, sub_self]
      · show (a 0 0 * a 0 1 - (p : B)) • tangent (γ 1) = 0
        have t1 := congrArg tangent (hPP (γ 1))
        rw [e1, map_add, endAct_homothety, endAct_verschiebungInt, e0] at t1
        simp only [map_add, tangent_homothety, tangent_verschiebungInt, smul_zero, add_zero, smul_smul, map_nsmul] at t1
        rw [mul_comm] at t1
        rw [sub_smul, t1, Nat.cast_smul_eq_nsmul, sub_self]

    set r : B := a 0 0 * a 0 1 - (p : B) with hr
    have hent : ∀ i k, r * tangent (γ i) k = 0 := fun i k => by
      have := congrFun (key i) k
      simpa [Pi.smul_apply, smul_eq_mul] using this
    have hdet : r * (Matrix.of fun i k => tangent (γ i) k).det = 0 := by
      rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply]
      rw [mul_sub, ← mul_assoc, ← mul_assoc, hent, hent, zero_mul, zero_mul, sub_self]
    exact sub_eq_zero.mp (hγ.2.mul_left_eq_zero.mp hdet)
  exact ⟨a, fun i N => H i N, hprod⟩

#print axioms solution

end S_CerednikDrinfeld_FormalODModule_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_hasStructureConstants_mul_eq_of_isHomogeneousVBasis (solution)
