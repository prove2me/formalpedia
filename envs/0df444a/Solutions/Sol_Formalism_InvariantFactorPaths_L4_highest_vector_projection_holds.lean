-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.highest_vector_projection_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:39.304803+00:00
-- url     : https://prove2.me/submissions/2c420a3b-f3f8-4347-a7d6-ceca00edd2ae

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjection
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_HighestVectorProjectionPos
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_trivial_projection_holds
import Theorems.Thm_Formalism_CountingSumsFrames_comm_wtsp
import Theorems.Thm_Formalism_CountingSumsFrames_eul_glAct
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_cons
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_fix
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_fock
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_int
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_keep
import Theorems.Thm_Formalism_CountingSumsFrames_pol_iff_eul
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
import Theorems.Thm_Formalism_GM_TM_mem_intPol_of_norm
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycond
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycondC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_free
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_keep_supp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_commC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_comm_later
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_glActC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_polC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typeProj_range_le_ycond
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_fix
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycond_fix
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_cartan_comm_erase__7d4a3ad236fe
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_fock_monomial_zero__a5d7011b8429
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_fock_right_zero__5b3a67430530
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_hwProj_comm__9e268cd004a7
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_monomial_mem_supp__96c2d3c392fb
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_L4_resL_fix__6bb06ae02750
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : HighestVectorProjectionPos := by
  classical
  intro p _ K r _ LL q J M ρ w e1 hK hr hρ hv hHP hHE
  obtain ⟨hP1, hP2⟩ := hHP
  obtain ⟨PE, hE1, hE2, hE3, hE4, hE5⟩ := hHE (K + 1) le_rfl w
  set v : Fin (K + 1) × Fin r := (Fin.last K, ρ) with hvdef
  set Wt := WtSpC p LL (K + 1) univ w with hWtdef

  let Cs : Fin (K + 2) → Finset (Fin r) := fun i => if (i : ℕ) = K + 1 then univ.erase ρ else univ
  let s : Fin (K + 2) → Finset (Fin q) := fun i =>
    univ.filter fun k => J k = (i : ℕ) ∨ (K ≤ (i : ℕ) ∧ K + 1 ≤ J k)
  let thr : Fin (K + 2) → WithTop ℤ := fun i => (s i).inf M
  let T : Fin (K + 2) → Set (Fin r → ℤ) := fun i => {la | ((la 0 : ℤ) : WithTop ℤ) ≤ thr i}
  have h0ρ : (0 : Fin r) ≠ ρ := by
    intro h
    have h' := congrArg Fin.val h
    have h0 : ((0 : Fin r) : ℕ) = 0 := by simp
    rw [hρ, h0] at h'
    omega
  have hCsT : ∀ i : Fin (K + 2), (i : ℕ) = K + 1 → Cs i = univ.erase ρ := fun i h => if_pos h
  have hCsL : ∀ i : Fin (K + 2), (i : ℕ) ≠ K + 1 → Cs i = univ := fun i h => if_neg h
  have hCs : ∀ i, Cs i = univ ∨ Cs i = univ.erase ρ := by
    intro i
    by_cases h : (i : ℕ) = K + 1
    · exact Or.inr (hCsT i h)
    · exact Or.inl (hCsL i h)
  have h0Cs : ∀ i, (0 : Fin r) ∈ Cs i := by
    intro i
    rcases hCs i with h | h <;> rw [h]
    · exact mem_univ _
    · exact mem_erase.mpr ⟨h0ρ, mem_univ _⟩
  have hsat : ∀ i, CsSaturated (Cs i) (T i) := fun i la la' h => by
    show ((la 0 : ℤ) : WithTop ℤ) ≤ thr i ↔ ((la' 0 : ℤ) : WithTop ℤ) ≤ thr i
    rw [h 0 (h0Cs i)]
  have hthrle : ∀ (i : Fin (K + 2)) (k : Fin q), (J k = (i : ℕ) ∨ (K ≤ (i : ℕ) ∧ K + 1 ≤ J k)) → thr i ≤ M k :=
    fun i k hk => Finset.inf_le (mem_filter.mpr ⟨mem_univ k, hk⟩)
  have hthrc : ∀ i : Fin (K + 2), thr i = ⊤ ∨
      ∃ k, (J k = (i : ℕ) ∨ (K ≤ (i : ℕ) ∧ K + 1 ≤ J k)) ∧ thr i = M k := by
    intro i
    rcases (s i).eq_empty_or_nonempty with he | hne
    · left
      show (s i).inf M = ⊤
      rw [he, Finset.inf_empty]
    · right
      obtain ⟨k, hk, hke⟩ := Finset.exists_mem_eq_inf (s i) hne M
      exact ⟨k, (mem_filter.mp hk).2, hke⟩
  have hex : ∀ i : Fin (K + 2), ∃ P, IsTypeProj p LL i (Cs i) (T i) P ∧
      (∀ F G, fock p (P F) G = fock p F (P G)) ∧
      ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P F ∈ IntPol p (Fin (K + 1) × Fin r) :=
    fun i => hP1 i (Nat.lt_succ_iff.mp i.isLt) (Cs i) (hCs i) (T i) (hsat i)
  choose P hPt hPsa hPint using hex
  have hPlow : ∀ i : Fin (K + 2), (i : ℕ) ≠ K + 1 → IsTypeProj p LL i univ (T i) (P i) := by
    intro i h
    have := hPt i
    rwa [hCsL i h] at this
  have hPtop : ∀ i : Fin (K + 2), (i : ℕ) = K + 1 → IsTypeProj p LL (K + 1) (univ.erase ρ) (T i) (P i) := by
    intro i h
    have := hPt i
    rwa [hCsT i h, h] at this
  have hPP : ∀ i x, P i (P i x) = P i x := fun i x => LinearMap.congr_fun (hPt i).1 x
  have hsub : ∀ i i' : Fin (K + 2), (i : ℕ) ≤ (i' : ℕ) → Cs i' ⊆ Cs i := by
    intro i i' h
    by_cases hi : (i : ℕ) = K + 1
    · rw [hCsT i hi, hCsT i' (by have := i'.isLt; omega)]
    · rw [hCsL i hi]; exact subset_univ _
  have hcomm : ∀ i i' x, P i (P i' x) = P i' (P i x) := by
    intro i i' x
    rcases le_total (i : ℕ) (i' : ℕ) with h | h
    · exact LinearMap.congr_fun (hP2 i i' (Cs i) (Cs i') (T i) (T i') (P i) (P i') h (hsub i i' h) (hCs i)
        (hCs i') (hPt i) (hPt i')) x
    · exact (LinearMap.congr_fun (hP2 i' i (Cs i') (Cs i) (T i') (T i) (P i') (P i) h (hsub i' i h) (hCs i')
        (hCs i) (hPt i') (hPt i)) x).symm
  have hPpol : ∀ i, ∀ x ∈ Pol p r LL, P i x ∈ Pol p r LL := fun i => typeProj_polC LL i (Cs i) (T i) (P i) (hPt i)

  have hPgl : ∀ i, ∀ c ∈ univ.erase ρ, ∀ d ∈ univ.erase ρ, ∀ x,
      P i (glAct p LL (K + 1) c d x) = glAct p LL (K + 1) c d (P i x) := by
    intro i c hc d hd x
    by_cases hi : (i : ℕ) = K + 1
    · exact typeProj_glActC LL (K + 1) _ (T i) (P i) (hPtop i hi) c hc d hd x
    · exact typeProj_comm_later LL i (K + 1) (Nat.lt_succ_iff.mp i.isLt) (T i) (P i) (hPlow i hi) c d x
  have hPcar : ∀ i c x, P i (glAct p LL (K + 1) c c x) = glAct p LL (K + 1) c c (P i x) := by
    intro i c x
    by_cases hi : (i : ℕ) = K + 1
    · by_cases hc : c = ρ
      · subst hc
        exact typeProj_commC LL (K + 1) _ (T i) (P i) (hPtop i hi) (glAct p LL (K + 1) c c)
          (fun a ha b hb x => cartan_comm_erase' LL (K + 1) c a ha b hb x) x
      · exact hPgl i c (mem_erase.mpr ⟨hc, mem_univ _⟩) c (mem_erase.mpr ⟨hc, mem_univ _⟩) x
    · exact typeProj_comm_later LL i (K + 1) (Nat.lt_succ_iff.mp i.isLt) (T i) (P i) (hPlow i hi) c c x
  have hPWt : ∀ i, ∀ x ∈ Wt, P i x ∈ Wt := fun i => comm_wtsp LL (K + 1) (P i) (hPcar i) w
  have hPres : ∀ i x, P i (resL p v 0 x) = resL p v 0 (P i x) := by
    intro i
    refine typeProj_commC LL i (Cs i) (T i) (P i) (hPt i) (resL p v 0) (fun c hc d hd x => ?_)
    refine resL_glAct LL i c d v 0 (fun i' hi' => ?_) x
    by_cases hi : (i : ℕ) = K + 1
    · rw [hCsT i hi] at hc hd
      exact ⟨fun h => Finset.ne_of_mem_erase hc (Prod.mk.inj h).2, fun h => Finset.ne_of_mem_erase hd (Prod.mk.inj h).2⟩
    · have hne : i' ≠ Fin.last K := by
        intro h
        rw [h, Fin.val_last] at hi'
        have := i.isLt
        omega
      exact ⟨fun h => hne (Prod.mk.inj h).1, fun h => hne (Prod.mk.inj h).1⟩
  have hPfree : ∀ i, ∀ x ∈ FreeOf p v, P i x ∈ FreeOf p v := by
    intro i x hx
    rw [← resL_fix' v x hx, hPres i x]
    exact resL_free v _

  have hEcomm := hwProj_comm' LL (K + 1) ρ w PE
  have hEP : ∀ i, ∀ x ∈ Wt, PE (P i x) = P i (PE x) := fun i => hEcomm (P i) hE1 hE2 hE3 (hPgl i) (hPWt i)
  have hEres : ∀ x ∈ Wt, PE (resL p v 0 x) = resL p v 0 (PE x) :=
    hEcomm (resL p v 0) hE1 hE2 hE3
      (fun c hc d hd x => resL_glAct LL (K + 1) c d v 0 (fun i' _ =>
        ⟨fun h => Finset.ne_of_mem_erase hc (Prod.mk.inj h).2, fun h => Finset.ne_of_mem_erase hd (Prod.mk.inj h).2⟩) x)
      (resL_keep_supp v 0 _)
  have hEeul : ∀ i0 : Fin (K + 1), ∀ x ∈ Wt, PE (ProjS.eulL (fun c : Fin r => (i0, c)) x) =
      ProjS.eulL (fun c : Fin r => (i0, c)) (PE x) := fun i0 =>
    hEcomm (ProjS.eulL (fun c : Fin r => (i0, c))) hE1 hE2 hE3
      (fun c _ d _ x => eul_glAct LL (K + 1) i0 c d x)
      (comm_wtsp LL (K + 1) _ (fun c x => eul_glAct LL (K + 1) i0 c c x) w)
  have hEfix : ∀ g ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ Wt, PE g = g := by
    intro g hg
    rw [← hE2] at hg
    obtain ⟨z, rfl⟩ := hg
    exact LinearMap.congr_fun hE1 z

  have hgfix : ∀ g ∈ XSp p LL J M ρ, ∀ i, P i g = g := by
    intro g hg i
    obtain ⟨hg1, hgI⟩ := Submodule.mem_inf.mp hg
    have hgP := (Submodule.mem_inf.mp hg1).1
    rw [Submodule.mem_iInf] at hgI
    by_cases hi : (i : ℕ) = K + 1
    · rcases hthrc i with ht | ⟨k, hk, ht⟩
      · refine ycondC_fix LL (K + 1) (univ.erase ρ) (mem_erase.mpr ⟨h0ρ, mem_univ _⟩) ⊤ (T i) (P i) (hPtop i hi)
          (fun la _ => ?_) g (Submodule.mem_inf.mpr ⟨?_, hgP⟩)
        · show ((la 0 : ℤ) : WithTop ℤ) ≤ thr i
          rw [ht]; exact le_top
        · refine le_ycondC LL (K + 1) (univ.erase ρ) ⊤ ⊤ (fun x _ => ?_) (fun _ _ _ _ _ _ => trivial) trivial
          rw [mem_restrictSupport_iff]
          intro m _
          exact (le_top : ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ ⊤)
      · have hk' : K + 1 ≤ J k := by omega
        have h1 := hgI k
        rw [if_pos hk'] at h1
        have h2 := (Submodule.mem_inf.mp h1).2
        have hT : T i = {la | ((la 0 : ℤ) : WithTop ℤ) ≤ M k} := by
          show {la : Fin r → ℤ | ((la 0 : ℤ) : WithTop ℤ) ≤ thr i} = _
          rw [ht]
        have h3 : g ∈ LinearMap.range (P i) := by
          rw [(hPtop i hi).2.1, hT]
          exact h2
        obtain ⟨z, rfl⟩ := h3
        exact hPP i z
    · refine ycond_fix LL i (T i) (thr i) (P i) (hPlow i hi) (fun la h => h) g (Submodule.mem_inf.mpr ⟨?_, hgP⟩)
      rcases hthrc i with ht | ⟨k, hk, ht⟩
      · rw [ht]
        refine le_ycond LL i ⊤ ⊤ (fun x _ => ?_) (fun _ _ _ _ => trivial) trivial
        rw [mem_restrictSupport_iff]
        intro m _
        exact (le_top : ((wt LL i 0 m : ℤ) : WithTop ℤ) ≤ ⊤)
      · rw [ht]
        have h1 := hgI k
        have := i.isLt
        rcases hk with hk | ⟨hk1, hk2⟩
        · rw [if_neg (by omega), hk] at h1
          exact h1
        · rw [if_pos hk2] at h1
          rw [show (i : ℕ) = K by omega]
          exact (Submodule.mem_inf.mp h1).1

  let Q := lcomp P (List.finRange (K + 2))
  let f : (Fin (K + 1) × Fin r →₀ ℕ) → MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] := fun m =>
    if (∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c) then PE (Q (monomial m 1)) else 0
  refine ⟨(basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f, fun m hm hmv => ?_⟩
  have hPr : (basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr ℚ_[p] f (monomial m 1) = f m := by
    have := (basisMonomials (Fin (K + 1) × Fin r) ℚ_[p]).constr_basis ℚ_[p] f m
    rwa [coe_basisMonomials] at this
  rw [hPr]
  by_cases hw : ∀ c ∈ (univ : Finset (Fin r)), wt LL (K + 1) c m = w c
  · rw [show f m = PE (Q (monomial m 1)) from if_pos hw]
    set u : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] := monomial m 1 with hu
    have huP : u ∈ Pol p r LL := monomial_mem_supp' _ m hm
    have huZ : u ∈ PolZ p r LL := by
      refine Submodule.mem_inf.mpr ⟨huP, mem_intPol_of_norm _ fun m' => ?_⟩
      rw [hu, coeff_monomial]; split_ifs <;> simp
    have huW : u ∈ Wt := monomial_mem_supp' _ m hw
    have huF : u ∈ FreeOf p v := monomial_mem_supp' _ m hmv
    set y := Q u with hy
    have hyW : y ∈ Wt := lcomp_keep P (Wt : Set _) _ (fun j _ => hPWt j) u huW
    have hyF : y ∈ FreeOf p v := lcomp_keep P (FreeOf p v : Set _) _ (fun j _ => hPfree j) u huF
    have hyP : y ∈ Pol p r LL := lcomp_keep P (Pol p r LL : Set _) _ (fun j _ => hPpol j) u huP
    have hyfix : ∀ i, P i y = y := fun i => lcomp_fix P hPP hcomm _ i (List.mem_finRange i) _

    have hl : List.finRange (K + 2) = 0 :: 1 :: ((List.finRange K).map Fin.succ).map Fin.succ := by
      rw [List.finRange_succ, List.finRange_succ]
      simp
    have hint0 := lcomp_int LL e1 P hPpol hPint (((List.finRange K).map Fin.succ).map Fin.succ) u huZ
    rw [List.length_map, List.length_map, List.length_finRange] at hint0
    have hy'P : lcomp P (((List.finRange K).map Fin.succ).map Fin.succ) u ∈ Pol p r LL :=
      lcomp_keep P (Pol p r LL : Set _) _ (fun j _ => hPpol j) u huP
    have hyy : y = lcomp P (((List.finRange K).map Fin.succ).map Fin.succ) u ∨ y = 0 := by
      have hy2 : y = P 0 (P 1 (lcomp P (((List.finRange K).map Fin.succ).map Fin.succ) u)) := by
        rw [hy]
        show lcomp P (List.finRange (K + 2)) u = _
        rw [hl, lcomp_cons, lcomp_cons, LinearMap.comp_apply, LinearMap.comp_apply]
      rw [hy2]
      rcases trivial_projection_holds p (K + 1) r LL _ (T 1) (P 1) (by simp) (by omega) (hPlow 1 (by simp; omega)) with h1 | h1
      · rw [h1 _ hy'P]
        rcases trivial_projection_holds p (K + 1) r LL _ (T 0) (P 0) (by simp) (by omega) (hPlow 0 (by simp)) with h0 | h0
        · exact Or.inl (h0 _ hy'P)
        · exact Or.inr (h0 _ hy'P)
      · rw [h1 _ hy'P, map_zero]
        exact Or.inr rfl
    have hint : ((p : ℚ_[p]) ^ (e1 * K)) • y ∈ PolZ p r LL := by
      rcases hyy with h | h
      · rw [h]; exact hint0
      · rw [h, smul_zero]; exact Submodule.zero_mem _
    set z := PE y with hz
    have hzfix : ∀ i, P i z = z := fun i => by rw [hz, ← hEP i y hyW, hyfix i]
    have hzR : z ∈ HWC p LL (K + 1) (univ.erase ρ) w ⊓ Wt := hE2 ▸ LinearMap.mem_range_self PE y
    have hzP : z ∈ Pol p r LL := by
      rw [pol_iff_eul] at hyP ⊢
      intro i
      rw [hz, ← hEeul i y hyW, hyP i, map_smul]
    have hzF : z ∈ FreeOf p v := by
      have h1 : resL p v 0 z = z := by rw [hz, ← hEres y hyW, resL_fix' v y hyF]
      rw [← h1]
      exact resL_free v z
    have hzX : z ∈ XSp p LL J M ρ := by
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hzP, hzF⟩, (Submodule.mem_iInf _).mpr fun k => ?_⟩
      split_ifs with hk
      · refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
        · have h1 := typeProj_range_le_ycond LL K (T ⟨K, by omega⟩) (M k) (P ⟨K, by omega⟩)
            (hPlow ⟨K, by omega⟩ (by simp))
            (fun la hla => le_trans hla (hthrle ⟨K, by omega⟩ k (Or.inr ⟨le_rfl, hk⟩))) z
          rwa [hzfix] at h1
        · have h1 : z ∈ LinearMap.range (P ⟨K + 1, by omega⟩) := ⟨z, hzfix _⟩
          rw [(hPtop ⟨K + 1, by omega⟩ rfl).2.1] at h1
          exact (iSup₂_le fun la hla => le_iSup₂_of_le (f := fun (la : Fin r → ℤ)
            (_ : ((la 0 : ℤ) : WithTop ℤ) ≤ M k) => IsoC p LL (K + 1) (univ.erase ρ) la) la
            (le_trans hla (hthrle ⟨K + 1, by omega⟩ k (Or.inr ⟨Nat.le_succ K, hk⟩))) le_rfl) h1
      · have h1 := typeProj_range_le_ycond LL (J k) (T ⟨J k, by omega⟩) (M k) (P ⟨J k, by omega⟩)
          (hPlow ⟨J k, by omega⟩ (by simp; omega))
          (fun la hla => le_trans hla (hthrle ⟨J k, by omega⟩ k (Or.inl rfl))) z
        rwa [hzfix] at h1
    refine ⟨Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hzX, (Submodule.mem_inf.mp hzR).1⟩,
      (Submodule.mem_inf.mp hzR).2⟩, ?_, ?_⟩
    · have h5 := hE5 _ hint (Wt.smul_mem _ hyW)
      rw [map_smul, smul_smul, ← pow_add] at h5
      rw [show (K + 1) * e1 = e1 + e1 * K by ring]
      exact h5
    · intro g hg
      obtain ⟨hg1, hgW⟩ := Submodule.mem_inf.mp hg
      obtain ⟨hgX, hgH⟩ := Submodule.mem_inf.mp hg1
      rw [hz, ← hE4 g y hgW hyW, hEfix g (Submodule.mem_inf.mpr ⟨hgH, hgW⟩)]
      exact lcomp_fock P hPsa g (hgfix g hgX) _ u
  · rw [show f m = 0 from if_neg hw]
    refine ⟨Submodule.zero_mem _, by rw [smul_zero]; exact Submodule.zero_mem _, fun g hg => ?_⟩
    rw [fock_right_zero', fock_monomial_zero']
    intro hmg
    have hgW := (Submodule.mem_inf.mp hg).2
    rw [WtSpC, mem_restrictSupport_iff] at hgW
    exact hw (hgW (Finset.mem_coe.mpr hmg))
end Formalism.InvariantFactorPaths.L4
