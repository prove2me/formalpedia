-- Prove2me | solution 1 for DetDLP.theorem_1_1_from_appendix_d
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T10:30:05.05681+00:00
-- url     : https://prove2.me/submissions/58c44b17-05a4-45c9-b924-e3522c248b9d

import Theorems.Thm_DetDLP_btn_parsimonious_count_and_stage1_cross_mul
import Theorems.Thm_DetDLP_ecdlp_short_weierstrass_reduction
import Theorems.Thm_DetDLP_fp_dlp_from_primitive_root_and_full_dlp
import Theorems.Thm_DetDLP_lemma_4_4_coset_update_halving
import Theorems.Thm_DetDLP_m3d_ec_stage2_driver_with_order_tm
import Theorems.Thm_DetDLP_m89_s1_count_oracle
import Theorems.Thm_DetDLP_modular_and_ec_gadget_parsimony
import Theorems.Thm_DetDLP_proposition_3_3_from_appendix_d
import Theorems.Thm_DetDLP_theorem_2_2_from_appendix_d
import Theorems.Thm_DetDLP_theorem_3_1_from_theorem_2_2
import Theorems.Thm_DetDLP_theorem_4_3_from_appendix_d
import Theorems.Thm_DetDLP_w3_ec_separator_btn
import Theorems.Thm_DetDLP_w3_fp_separator_btn
import Theorems.Thm_DetDLP_m3c_fp_stage2_driver_from_counts
import Theorems.Thm_DetDLP_w3_stage2_abstract_coset_recovery

set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT.Computation

private theorem w3_terminal_contraction (hOAI : OpenAIAppendixDPremise) {fam : w3_Query → Prop}
    (C c : ℕ) (eval : PrimitiveMachine) (oe : Fin eval.tapeCount)
    (hC : 0 < C) (hc : 0 < c) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ q, fam q → ∀ n : w3_Net q C,
        n.G.nV ≤ (n.S+n.desc.length+1)^c →
        BTNEntryEvaluable n.desc n.G (w3_precision q) (w3_len q) n.T eval oe
          (polyBound c (n.S+n.desc.length)) (polyBound c (n.S+n.desc.length)) →
        ∃ w, EncodesTruncPoly (w3_precision q) (w3_len q) w (BTNContract n.G n.T) ∧
          RunsWithin M out (w3_packet n) w
            (polyBound K (n.S+n.desc.length) * mainTimeBound K q.b)
            (polyBound K (n.S+n.desc.length)) := by
  obtain ⟨M,out,K,hcontract⟩ := theorem_4_3_from_appendix_d hOAI C c hC hc eval oe
  refine ⟨M,out,K,fun q _ n hV heval => ?_⟩
  rcases n.shape with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩
  obtain ⟨w,hw,hr⟩ := hcontract q.b q.m q.k n.S (w3_precision q) (w3_len q) n.desc n.G n.T
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hV n.spec heval
  exact ⟨w,hw,by simpa [w3_packet] using hr⟩

private theorem witnessedTerminal (hOAI : OpenAIAppendixDPremise) (fam : w3_Query → Prop) (hsep : w3_Separator fam) :
    ∃ (C c : ℕ) (build : PrimitiveMachine) (ob : Fin build.tapeCount)
      (eval : PrimitiveMachine) (oe : Fin eval.tapeCount)
      (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      0 < C ∧ 0 < c ∧
      ∀ q, fam q → ∃ n : w3_Net q C,
        RunsWithin build ob q.input (w3_packet n)
          (polyBound c q.input.length) (polyBound c q.input.length) ∧
        BTNEntryEvaluable n.desc n.G (w3_precision q) (w3_len q) n.T eval oe
          (polyBound c (n.S+n.desc.length)) (polyBound c (n.S+n.desc.length)) ∧
        ∃ w, EncodesTruncPoly (w3_precision q) (w3_len q) w (BTNContract n.G n.T) ∧
          RunsWithin M out (w3_packet n) w
            (polyBound K (n.S+n.desc.length) * mainTimeBound K q.b)
            (polyBound K (n.S+n.desc.length)) := by
  rcases hsep with ⟨C,c,build,ob,eval,oe,hC,hc,hbuild⟩
  obtain ⟨M,out,K,hcontract⟩ := w3_terminal_contraction hOAI C c eval oe hC hc
  refine ⟨C,c,build,ob,eval,oe,M,out,K,hC,hc,fun q hq => ?_⟩
  obtain ⟨n,hV,hbuild',heval⟩ := hbuild q hq
  exact ⟨n,hbuild',heval,hcontract q hq n hV heval⟩

set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

private theorem w3_update_subroutine : w3_hnfOps := by
  obtain ⟨D,o,K,H⟩ := lemma_4_4_coset_update_halving
  refine ⟨D,o,K,?_⟩
  intro M N nz hM hN s r hb hcon
  obtain ⟨x,B,hB,hA,_,hrun,hh⟩ := H M N hM hN s.1 s.2 r.1 r.2 hb hcon
  refine ⟨(x,B),⟨hB,hA⟩,fun hv => ?_,hrun⟩
  change 2 * Nat.card (affineCoset M x B) ≤ _
  rw [hA]; exact (hh hv).2

private theorem w3_index_pair {V : Type} [AddCommGroup V] {m : ℕ}
    (FB : IndexedFactorBase V m) (g : V) (A B : Fin m → V)
    (hm : ∀ i, A i ∈ FB.blocks i ∧ B i ∈ FB.blocks i) (hs : (∑ i, (A i+B i)) = g) :
    ∃ X : FB.BlockTuple, FB.tupleVal X = g := by
  classical
  choose a ha using fun i => List.mem_iff_get.mp (hm i).1
  choose b hb using fun i => List.mem_iff_get.mp (hm i).2
  refine ⟨fun i j => if j = 0 then a i else b i,?_⟩
  change (∑ i, ((FB.blocks i).get (a i) + (FB.blocks i).get (b i))) = g
  simpa only [ha,hb] using hs

private theorem w3_finish_trace {V : Type} [AddCommGroup V] [Fintype V] [DecidableEq V]
    {M m : ℕ} [NeZero M] (hm : 2 ≤ m) (hM : 2 ≤ M) (hcard : Nat.card V = M)
    (P Q : V) (hg : addOrderOf P = M) (ref native : IndexedFactorBase V m)
    (cover : ∀ g : V, ∃ X : ref.BlockTuple, ref.tupleVal X = g) (accepts : ℕ → Prop)
    (h : w3_traceOutput ref native M P Q accepts) : ∃ u, u < M ∧ u • P = Q ∧ accepts u := by
  obtain ⟨himage,U,y,hU,hout,hrun⟩ := h
  have cov (g : V) : ∃ X : native.BlockTuple, native.tupleVal X = g := himage (cover g)
  have htop : AddSubgroup.zmultiples P = ⊤ := (AddSubgroup.zmultiples P).eq_top_of_card_eq
    ((Nat.card_zmultiples P).trans (hg.trans hcard.symm))
  have hall (v : V) : v ∈ AddSubgroup.zmultiples P := by rw [htop]; trivial
  let e := (zmodAddEquivOfGenerator hall hcard).symm
  have hP : e P = 1 := zmodAddEquivOfGenerator_symm_apply_generator hall hcard
  obtain ⟨_,hcorrect⟩ := w3_stage2_abstract_coset_recovery M hM P Q e hP hm native cov U hU
  obtain ⟨_,hu,he⟩ := hcorrect y hout
  exact ⟨(y native.targetCoord).val,hu,he,hrun⟩

private theorem w3_finish_scan {V : Type} [AddMonoid V] [DecidableEq V] {M : ℕ}
    {P Q : V} {accepts : ℕ → Prop} (h : w3_scanOutput M P Q accepts) :
    ∃ u, u < M ∧ u • P = Q ∧ accepts u := by
  obtain ⟨u,hu,hr⟩ := h
  have hit := List.find?_some (p := fun j : ℕ => decide (j • P = Q)) hu
  exact ⟨u,List.mem_range.mp (List.mem_of_find?_eq_some hu), of_decide_eq_true hit,hr⟩

private theorem stageCounts (hOAI : OpenAIAppendixDPremise) : M89S1.CountOracle :=
  m89_s1_count_oracle btn_parsimonious_count_and_stage1_cross_mul modular_and_ec_gadget_parsimony
    (theorem_2_2_from_appendix_d hOAI)

private theorem solveEc (hOAI : OpenAIAppendixDPremise) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
          letI := ecPointFintype E
          let r := Fintype.card E.toAffine.Point
          r.Prime →
          ∀ (P Q : E.toAffine.Point),
            addOrderOf P = r →
            ∃ x : ℕ, x < r ∧ x • P = Q ∧
              RunsWithin M out (encodeECDLPInput p E P Q) (countWord x)
                (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p)) := by
  classical
  obtain ⟨en,eo,de,od,K,hstage⟩ := (theorem_3_1_from_theorem_2_2 (theorem_2_2_from_appendix_d hOAI)).1
  have hn : w3_terminalOps w3_ecQueries := witnessedTerminal hOAI _ w3_ec_separator_btn
  obtain ⟨D,o,C,hr⟩ := m3d_ec_stage2_driver_with_order_tm (stageCounts hOAI) en eo de od K hn w3_update_subroutine
  refine ⟨D,o,C,?_⟩
  intro p hp h3 E hE ha₁ ha₂ ha₃
  let _ := ecPointFintype E
  let M := Fintype.card E.toAffine.Point
  let m := blockCount (bitLen p)
  dsimp only
  intro hprime P Q hg
  obtain ⟨hsmall,hlarge⟩ := hr p h3 E ha₁ ha₂ ha₃ hprime P Q hg
  by_cases hreg : w3_large p M
  · obtain ⟨F,hF⟩ := hstage p h3 E
    obtain ⟨_,B,_,htrace⟩ := hlarge hreg F hF
    have cov (g : E.toAffine.Point) : ∃ X : (IndexedFactorBase.mk F).BlockTuple,
        (IndexedFactorBase.mk F).tupleVal X = g := by
      obtain ⟨A,B',hm,hs,_⟩ := hF.2.2.2.2 g
      exact w3_index_pair ⟨F⟩ g A B' hm hs
    exact w3_finish_trace (le_max_left 2 _) (by have := hreg.2.1; omega) Nat.card_eq_fintype_card
      P Q hg ⟨F⟩ ⟨B⟩ cov _ htrace
  · exact w3_finish_scan (hsmall hreg)


private theorem solveFp (hOAI : OpenAIAppendixDPremise) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ),
        orderOf h = p - 1 →
        ∃ u : ℕ, u < p - 1 ∧ h ^ u = a ∧
          RunsWithin M out (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val) (countWord u)
            (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p)) := by
  classical
  obtain ⟨en,eo,de,od,K,hstage⟩ := (theorem_3_1_from_theorem_2_2 (theorem_2_2_from_appendix_d hOAI)).2
  have hn : w3_terminalOps w3_fpQueries := witnessedTerminal hOAI _ w3_fp_separator_btn
  obtain ⟨D,o,C,hr⟩ := m3c_fp_stage2_driver_from_counts (stageCounts hOAI) en eo de od K hn w3_update_subroutine
  refine ⟨D,o,C,?_⟩
  intro p hp h a hg
  let M := p-1
  let m := blockCount (bitLen p)
  obtain ⟨hsmall,hlarge⟩ := hr p h a hg
  suffices result : ∃ u, u < M ∧ u • Additive.ofMul h = Additive.ofMul a ∧
      RunsWithin D o (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val) (countWord u)
        (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p)) by
    obtain ⟨u,hu,he,ht⟩ := result
    exact ⟨u,hu,he,ht⟩
  by_cases hreg : w3_large p M
  · let _ : NeZero M := ⟨by have := hreg.2.1; omega⟩
    obtain ⟨F,hF⟩ := hstage p
    obtain ⟨_,B,_,htrace⟩ := hlarge hreg F hF
    have cov (g : Additive (ZMod p)ˣ) : ∃ X : (w3_fpFB F).BlockTuple, (w3_fpFB F).tupleVal X = g := by
      obtain ⟨A,B',hm,hs,_⟩ := hF.2.2.2.2 g.toMul
      apply w3_index_pair (w3_fpFB F) g (fun i => Additive.ofMul (A i)) (fun i => Additive.ofMul (B' i))
      · intro i
        exact ⟨List.mem_map.mpr ⟨A i,(hm i).1,rfl⟩,List.mem_map.mpr ⟨B' i,(hm i).2,rfl⟩⟩
      · exact hs
    have hc : Nat.card (Additive (ZMod p)ˣ) = M := by
      change Nat.card (ZMod p)ˣ = p-1
      rw [Nat.card_eq_fintype_card, ZMod.card_units]
    exact w3_finish_trace (le_max_left 2 _) (by have := hreg.2.1; omega) hc
      (Additive.ofMul h) (Additive.ofMul a) hg (w3_fpFB F) (w3_fpFB B) cov _ htrace
  · exact w3_finish_scan (hsmall hreg)


set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP

private lemma mul_dlog_unique {G : Type*} [Group G] {g : G} {x y : ℕ}
    (hx : x < orderOf g) (hy : y < orderOf g) (hxy : g ^ y = g ^ x) : y = x := by
  have hmod : y ≡ x [MOD orderOf g] := pow_eq_pow_iff_modEq.mp hxy
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hy, Nat.mod_eq_of_lt hx] at hmod

theorem solution (hOAI : OpenAIAppendixDPremise) :
    (∃ (M_ec : PrimitiveMachine) (out_ec : Fin M_ec.tapeCount) (C_ec : ℕ),
      ∀ (p : ℕ) [Fact p.Prime], 3 < p →
        ∀ (E : WeierstrassCurve (ZMod p)) [E.IsElliptic],
          letI := ecPointFintype E
          let r := Fintype.card E.toAffine.Point
          r.Prime →
          ∀ (P Q : E.toAffine.Point),
            addOrderOf P = r →
            ∃ x : ℕ, x < r ∧ x • P = Q ∧
              (∀ y : ℕ, y < r → y • P = Q → y = x) ∧
              RunsWithin M_ec out_ec (encodeECDLPInput p E P Q) (countWord x)
                (mainTimeBound C_ec (bitLen p)) (mainSpaceBound C_ec (bitLen p))) ∧
    (∃ (M_fp : PrimitiveMachine) (out_fp : Fin M_fp.tapeCount) (C_fp : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (g t : (ZMod p)ˣ),
        (t ∉ Subgroup.zpowers g →
          RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
            (encodeOptionNatBin none)
            (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p))) ∧
        (t ∈ Subgroup.zpowers g →
          ∃ x : ℕ, x < orderOf g ∧ g ^ x = t ∧
            (∀ y : ℕ, y < orderOf g → g ^ y = t → y = x) ∧
            RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
              (encodeOptionNatBin (some x))
              (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p)))) := by
  constructor
  · obtain ⟨M_ec, out_ec, C_ec, h_ec⟩ :=
      ecdlp_short_weierstrass_reduction (solveEc hOAI)
    refine ⟨M_ec, out_ec, C_ec, ?_⟩
    intro p hp hp3 E hE
    dsimp only
    intro hr P Q hP
    obtain ⟨x, hxr, hxQ, hrun⟩ := h_ec p hp3 E hr P Q hP
    refine ⟨x, hxr, hxQ, ?_, hrun⟩
    intro y hyr hyQ
    have hm : y ≡ x [MOD addOrderOf P] := nsmul_eq_nsmul_iff_modEq.mp (hyQ.trans hxQ.symm)
    rwa [Nat.ModEq, hP, Nat.mod_eq_of_lt hyr, Nat.mod_eq_of_lt hxr] at hm
  · obtain ⟨M_fp, out_fp, C_fp, h_fp⟩ :=
      fp_dlp_from_primitive_root_and_full_dlp
        (proposition_3_3_from_appendix_d hOAI)
        (solveFp hOAI)
    refine ⟨M_fp, out_fp, C_fp, ?_⟩
    intro p hp g t
    obtain ⟨hnot, hmem⟩ := h_fp p g t
    refine ⟨hnot, ?_⟩
    intro ht
    obtain ⟨x, hxord, hxt, hrun⟩ := hmem ht
    refine ⟨x, hxord, hxt, ?_, hrun⟩
    intro y hyord hyt
    exact mul_dlog_unique hxord hyord (hyt.trans hxt.symm)
