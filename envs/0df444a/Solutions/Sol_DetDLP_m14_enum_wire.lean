-- Prove2me | solution 1 for DetDLP.m14_enum_wire
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T07:46:34.446739+00:00
-- url     : https://prove2.me/submissions/97553fc0-7c85-4aba-ae7d-0d470b022860

import Definitions.Def_DetDLP_D4SoloPlanDefs
import Theorems.Thm_DetDLP_m89_polyT_oracle_loop
import Theorems.Thm_DetDLP_d4_padded_tree_rank_walker_v2_machine
import Theorems.Thm_DetDLP_m14_sync
import Theorems.Thm_DetDLP_m14_base_fuel

set_option autoImplicit false
set_option maxHeartbeats 800000

open Groundwork Polynomial Finset DetDLP DetDLP.AppendixD4 DetDLP.ResidualScalarOracle
open DetDLP.D4Plan DetDLP.D4StoppedNode DetDLP.D4RankWalker DetDLP.D4GuardTree
open DetDLP.D4SoloRaw DetDLP.D4SoloNode DetDLP.D4SoloRoot DetDLP.D4SoloStep
open DetDLP.D4SoloStepEq DetDLP.D4SoloTree DetDLP.D4SoloForest DetDLP.D4SoloPlanDefs
open DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.M14EnumWireInternal

noncomputable section

section OneCallCompiler

private theorem parse_aux_loc (x xs acc : Wd) : ∀ (fuel : Wd), x.length ≤ fuel.length →
    fuel.foldl advance (acc, Encoding.frame x ++ xs) = (x.reverse ++ acc, false :: xs) := by
  induction x generalizing acc with
  | nil => intro fuel _; induction fuel <;> simp_all [Encoding.frame, advance, List.foldl]
  | cons b x ih =>
    intro fuel hf
    cases fuel with
    | nil => simp at hf
    | cons _ fuel =>
      simpa [Encoding.frame, advance, List.foldl, List.append_assoc] using
        ih (b :: acc) fuel (by simpa using hf)

private theorem flen_loc (x : Wd) : (Encoding.frame x).length = 2 * x.length + 1 := by
  induction x with
  | nil => rfl
  | cons _ x ih => change (Encoding.frame x).length + 1 + 1 = 2 * (x.length + 1) + 1; omega

private theorem parsed_callPair (s a : Wd) : parse (true :: callPair s a) = (s.reverse, false :: a) := by
  simp only [parse, callPair, frame_correct, List.tail_cons]
  rw [parse_aux_loc]
  · simp
  · simp [flen_loc]; omega

private theorem first_callPair (s a : Wd) : first (true :: callPair s a) = s := by
  simp [first, parsed_callPair]

private theorem more_callPair (s a : Wd) : more (true :: callPair s a) = a := by
  simp [more, parsed_callPair]

attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.id'
  first_poly more_poly frame_poly poly_pack
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cond__4c673073da15
  P2M_Groundwork_PolyT_cons__3a60f43a3b86 PolyT.append PolyT.isEmpty

private theorem soloCallStep_poly {pre post : Wd → Wd} (hp : PolyT pre) (hq : PolyT post) :
    PolyT (soloCallStep pre post) := by
  unfold soloCallStep callPair
  have hs : PolyT (fun w : Wd => first (true :: w)) := by fun_prop
  have ha : PolyT (fun w : Wd => more (true :: w)) := by fun_prop
  have hp_s : PolyT (fun w : Wd => pre (first (true :: w))) := hp.comp hs
  have hpack_sa : PolyT (fun w : Wd => pack [first (true :: w), more (true :: w)]) :=
    poly_pack (P2M_Groundwork_PolyT_cons__3a60f43a3b86 hs
      (P2M_Groundwork_PolyT_cons__3a60f43a3b86 ha (PolyT.const [])))
  have hq_sa : PolyT (fun w : Wd => post (pack [first (true :: w), more (true :: w)])) :=
    hq.comp hpack_sa
  exact P2M_Groundwork_PolyT_cond__4c673073da15
    (PolyT.isEmpty ha)
    (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const false)
      (PolyT.append (frame_poly hs) hp_s))
    (P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const true) hq_sa)

/-- Uniform 1-call saved-input wrapper around `m89_polyT_oracle_loop`. -/
theorem soloOneCall (O : PrimitiveMachine) (o : Fin O.tapeCount)
    (pre post : Wd → Wd) (hp : PolyT pre) (hq : PolyT post) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      1 ≤ K ∧
      ∀ (q ans : Wd) (τ σ : ℝ) (M_len : ℕ),
        0 ≤ τ → 0 ≤ σ → ans ≠ [] →
        RunsWithin O o (pre q) ans τ σ →
        (callPair q []).length ≤ M_len →
        (callPair q (pre q)).length ≤ M_len →
        (callPair q ans).length ≤ M_len →
        ans.length ≤ M_len →
        (post (pack [q, ans])).length ≤ M_len →
        RunsWithin M out q (post (pack [q, ans]))
          (2 * (polyBound K M_len + (K : ℝ) * (τ + σ + 1)))
          (polyBound K M_len + (K : ℝ) * (σ + 1)) := by
  obtain ⟨M, out, K, hK1, run⟩ := m89_polyT_oracle_loop (soloCallStep pre post) (soloCallStep_poly hp hq) O o
  refine ⟨M, out, K, hK1, ?_⟩
  intro q ans τ σ M_len ht hs hne hO h1 h2 h3 h4 h5
  simpa using run τ σ ht hs 2 M_len q (post (pack [q, ans])) (by decide)
    (Or.inr ⟨q, pre q, ans, by change soloCallStep pre post (callPair q []) = false :: callPair q (pre q); simp [soloCallStep, first_callPair, more_callPair],
      h1, h2, h4, hO,
      Or.inl ⟨by
        change soloCallStep pre post (callPair q ans) = true :: post (pack [q, ans])
        unfold soloCallStep
        rw [first_callPair, more_callPair]
        cases ans with
        | nil => exact False.elim (hne rfl)
        | cons _ _ => rfl,
        h3, h5⟩⟩)

end OneCallCompiler

section WireEqualities

private theorem reattach_old_eq {C c : ℕ} (x : Input C c) (n : ℕ)
    (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n)
    (old : Fin x.spec.lookupVerts.card ≃ ↥x.spec.lookupVerts)
    (lp : (v : Fin x.spec.lookupVerts.card) →
      Fin (x.G.deg (old v).val) ≃ Fin ((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).deg (v.castAdd n)))
    (hlp : ∀ v i,
      D4CoreCut.origB x.G x.spec.lookupVerts
        (((D4CoreCut.reattach x.G x.spec.lookupVerts n leafFn).ports (v.castAdd n)).get (lp v i)) =
      (x.G.ports (old v).val).get i)
    (v : Fin x.spec.lookupVerts.card) :
    (old v).val = (D4CoreCut.lookupVerts x.G x.spec.lookupVerts)[v.val]'(by
      rw [D4CoreCut.lookup_length]; exact v.isLt) := by
  let L := x.spec.lookupVerts
  let H := D4CoreCut.reattach x.G L n leafFn
  have hdeg_pos : 0 < x.G.deg (old v).val := by
    rw [x.spec.lookup_deg (old v).val (old v).property]; exact x.hk
  let i₀ : Fin (x.G.deg (old v).val) := ⟨0, hdeg_pos⟩
  let e_b : Fin H.nE := (H.ports (v.castAdd n)).get (lp v i₀)
  have hincH := D4CoreCut.port_inc H (v.castAdd n) (lp v i₀)
  have hleft : D4CoreCut.lookupIdx x.G L e_b = v := by
    rcases hincH with h1 | h2
    · have hv : (D4CoreCut.lookupIdx x.G L e_b).val = v.val := by
        simpa [H, D4CoreCut.reattach, e_b] using congrArg Fin.val h1
      exact Fin.ext hv
    · have hlt : (v.castAdd n).val < L.card := v.isLt
      have hge : L.card ≤ ((H.endpoints e_b).2).val := by simp [H, D4CoreCut.reattach]
      rw [h2] at hge
      exact False.elim (Nat.not_lt_of_ge hge hlt)
  have he_eq : D4CoreCut.origB x.G L e_b = (x.G.ports (old v).val).get i₀ := hlp v i₀
  have hincG := D4CoreCut.port_inc x.G (old v).val i₀
  rw [← he_eq] at hincG
  have hind := D4CoreCut.independent_of_spec x.G x.spec
  have hsel : (if (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 ∈ L then
      (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 else
      (x.G.endpoints (D4CoreCut.origB x.G L e_b)).2) = (old v).val := by
    rcases hincG with h1 | h2
    · rw [h1, if_pos (old v).property]
    · rw [h2]
      by_cases h1in : (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 ∈ L
      · exact False.elim (hind (D4CoreCut.origB x.G L e_b) h1in (h2 ▸ (old v).property))
      · rw [if_neg h1in]
  have hidx_v : (D4CoreCut.lookupVerts x.G L).idxOf (old v).val = v.val := by
    have hv' := congrArg Fin.val hleft
    unfold D4CoreCut.lookupIdx at hv'
    change List.idxOf (if (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 ∈ L then
      (x.G.endpoints (D4CoreCut.origB x.G L e_b)).1 else
      (x.G.endpoints (D4CoreCut.origB x.G L e_b)).2) (D4CoreCut.lookupVerts x.G L) = v.val at hv'
    rwa [hsel] at hv'
  have hv_lt : v.val < (D4CoreCut.lookupVerts x.G L).length := by
    rw [D4CoreCut.lookup_length]; exact v.isLt
  have hget := List.getElem_idxOf (h := by rwa [hidx_v])
  conv_lhs => rw [← hget]
  congr 1

private theorem finRange_map_val (n : ℕ) : (List.finRange n).map Fin.val = List.range n :=
  List.ext_getElem (by simp) (fun i _ _ => by simp)

private theorem map_filter_comp_loc {α β : Type} (g : α → β) (p : β → Bool) (xs : List α) :
    (xs.filter (p ∘ g)).map g = (xs.map g).filter p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : p (g x) <;> simp [h, ih]

private theorem fin_addCases_ofFn {α : Type} {m n : ℕ} (f₁ : Fin m → α) (f₂ : Fin n → α) :
    List.ofFn (Fin.addCases f₁ f₂) = List.ofFn f₁ ++ List.ofFn f₂ := by
  apply List.ext_getElem
  · simp
  · intro idx h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn]
    by_cases hlt : idx < m
    · have hcast : (⟨idx, h1⟩ : Fin (m + n)) = Fin.castAdd n ⟨idx, hlt⟩ := rfl
      rw [hcast, Fin.addCases_left, List.getElem_append_left (by simp [hlt])]
      simp
    · have hge : m ≤ idx := Nat.le_of_not_lt hlt
      have hsub : idx - m < n := by omega
      have hnat : (⟨idx, h1⟩ : Fin (m + n)) = Fin.natAdd m ⟨idx - m, hsub⟩ := by
        apply Fin.ext; simp [Nat.add_sub_of_le hge]
      rw [hnat, Fin.addCases_right, List.getElem_append_right (by simp [hge])]
      simp

theorem lookupDescsRaw_eq {C c : ℕ} (x : Input C c) (n : ℕ)
    (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n) (degF l qPrec : ℕ) :
    let w_re := getReattachWit x n leafFn
    lookupDescsRaw x.desc (D4Slice.field 8 (D4Plan.input x)) degF l qPrec =
      List.ofFn (fun v : Fin x.spec.lookupVerts.card =>
        lookupDesc x.desc (w_re.old v).val.val degF l qPrec) := by
  intro w_re
  let L := x.spec.lookupVerts
  let mask := List.ofFn (fun v : Fin x.G.nV => decide (v ∈ L))
  obtain ⟨_, _, _, _, _, _, _, _, hfield8⟩ := DetDLP.m14_base_fuel.2.2.1 x
  rw [hfield8]
  unfold lookupDescsRaw
  have hlen_m : mask.length = x.G.nV := by simp [mask]
  rw [hlen_m, ← finRange_map_val x.G.nV,
      ← map_filter_comp_loc Fin.val (fun v => mask.getD v false) (List.finRange x.G.nV)]
  have hflt : (List.finRange x.G.nV).filter ((fun v => mask.getD v false) ∘ Fin.val) =
      D4CoreCut.lookupVerts x.G L := by
    unfold D4CoreCut.lookupVerts
    congr 1; funext v
    simp only [Function.comp_apply, mask]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [v.isLt]),
        List.getElem_ofFn, Option.getD_some]
  rw [hflt]
  apply List.ext_getElem
  · simp [D4CoreCut.lookup_length x.G L, L]
  · intro idx h1 h2
    simp only [List.length_ofFn] at h2
    simp only [List.getElem_map, List.getElem_ofFn]
    have hold := reattach_old_eq x n leafFn w_re.old w_re.lp w_re.hlp ⟨idx, h2⟩
    rw [hold]
    rfl

theorem findBoundaryLeaf_eq_hitLeafFn {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (doneNodes : List (SoloNode x f PktOK))
    (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k)))
    (bi : Fin (4 * x.m * x.k)) :
    findBoundaryLeaf (doneNodes.map (·.toWorkItem.bits)) bi.val =
      (hitLeafFn x hbLen doneNodes hperm (bi.cast hbLen.symm)).val := by
  let doneList := doneNodes.map (·.toWorkItem.bits)
  let j₀ := hitLeafFn x hbLen doneNodes hperm (bi.cast hbLen.symm)
  have hcast : (bi.cast hbLen.symm).cast hbLen = bi := Fin.ext rfl
  have huniq := Classical.choose_spec (unique_leaf_of_pinFirsts_perm doneNodes hperm ((bi.cast hbLen.symm).cast hbLen))
  change (∃ kp, ((doneNodes.get j₀).pins.get kp).1 = _) ∧
    (∀ j', (∃ kp, ((doneNodes.get j').pins.get kp).1 = _) → j' = j₀) at huniq
  rw [hcast] at huniq
  have hpred_j : ∀ j' : Fin doneNodes.length,
      (((unpack (fld (doneList.getD j'.val []) 3)).any
        (fun pin => decide ((ints pin).getD 0 0 = bi.val))) = true ↔ j' = j₀) := by
    intro j'
    have hget_dl : doneList.getD j'.val [] = (doneNodes.get j').toWorkItem.bits := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [doneList, j'.isLt]),
          List.getElem_map, Option.getD_some]
      rfl
    have hunp : unpack (fld (doneNodes.get j').toWorkItem.bits 3) =
        (doneNodes.get j').pins.map (fun pv => encodeNatListBin [pv.1.val, pv.2.val]) := by
      unfold SoloNode.toWorkItem WorkItem.bits
      simp [fld_pack, unpack_pack]
    rw [hget_dl, hunp]
    simp only [List.any_eq_true, List.mem_map, decide_eq_true_eq]
    constructor
    · rintro ⟨_, ⟨pv, hpv, rfl⟩, hval⟩
      simp only [ints_encodeNatListBin, List.getD_cons_zero] at hval
      obtain ⟨kp, hkp⟩ := List.mem_iff_get.mp hpv
      have hbi : ((doneNodes.get j').pins.get kp).1 = bi := Fin.ext (by rw [hkp]; exact hval)
      exact huniq.2 j' ⟨kp, hbi⟩
    · rintro rfl
      obtain ⟨kp, hkp⟩ := huniq.1
      refine ⟨_, ⟨(doneNodes.get j₀).pins.get kp, List.get_mem _ kp, rfl⟩, ?_⟩
      simp only [ints_encodeNatListBin, List.getD_cons_zero]
      exact congrArg Fin.val hkp
  have hpred_iff : ∀ idx : ℕ, idx < doneNodes.length →
      (((unpack (fld (doneList.getD idx []) 3)).any
        (fun pin => decide ((ints pin).getD 0 0 = bi.val))) = true ↔ idx = j₀.val) := by
    intro idx hidx
    exact (hpred_j ⟨idx, hidx⟩).trans ⟨congrArg Fin.val, fun h => Fin.ext h⟩
  unfold findBoundaryLeaf
  have hdl_len : doneList.length = doneNodes.length := List.length_map _
  change ((List.range doneList.length).filter _).headD doneList.length = j₀.val
  rw [hdl_len]
  have hmem_flt : ∀ idx : ℕ, idx ∈ (List.range doneNodes.length).filter
      (fun idx => (unpack (fld (doneList.getD idx []) 3)).any
        (fun pin => decide ((ints pin).getD 0 0 = bi.val))) ↔ idx = j₀.val := by
    intro idx
    simp only [List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hlt, hp⟩
      exact (hpred_iff idx hlt).mp hp
    · rintro rfl
      exact ⟨j₀.isLt, (hpred_iff j₀.val j₀.isLt).mpr rfl⟩
  cases hfl : (List.range doneNodes.length).filter
      (fun idx => (unpack (fld (doneList.getD idx []) 3)).any
        (fun pin => decide ((ints pin).getD 0 0 = bi.val))) with
  | nil =>
    exfalso
    have h0 := (hmem_flt j₀.val).mpr rfl
    rw [hfl] at h0
    cases h0
  | cons a as =>
    have ha : a = j₀.val := (hmem_flt a).mp (by rw [hfl]; simp)
    subst ha
    simp

private theorem residue_zero_eq_encode (f : ℤ[X]) (l qPrec : ℕ) (hf : f.Monic) :
    encodeNatListBin ((List.range (l * f.natDegree)).map fun _ => 0) =
      residue f l qPrec hf 0 := by
  unfold residue word
  congr 1
  apply List.ext_getElem
  · simp
  · intro idx _ _
    simp [map_zero]

private theorem ctxRaw_eq_contextV2 (fuel : List Unit) (S m p guard l : ℕ) (fBits : Wd)
    (hD : Nat.clog 32 (4 * m) ≤ fuel.length)
    (hqp : guard + p ≤ fuel.length)
    (hl : l ≤ fuel.length)
    (hsh : ∀ d, 64 ^ D3Stopped.shift S d ≤ fuel.length) :
    ctxRaw fuel S m p guard l fBits = contextV2 S m p guard l fBits := by
  unfold ctxRaw contextV2
  dsimp only [letFun]
  rw [rangeFuel_eq fuel (Nat.clog 32 (4 * m)) hD,
      unaryFuelRep_eq fuel (guard + p) true hqp,
      unaryFuelRep_eq fuel l true hl]
  have hrows : (List.range (Nat.clog 32 (4 * m))).map (rowRaw fuel S) =
      (List.range (Nat.clog 32 (4 * m))).map (row S) := by
    apply List.ext_getElem
    · simp
    · intro d _ _
      simp only [List.getElem_map, List.getElem_range]
      unfold rowRaw row
      dsimp only [letFun]
      rw [unaryFuelRep_eq fuel (64 ^ D3Stopped.shift S d) true (hsh d)]
  rw [hrows]

/-- `preWalkGen` on `rankQuery x j` produces the exact initial state `startV2` of the rank walker. -/
theorem preWalkGen_eq_startV2 {C c : ℕ} (x : Input C c) (hL_level : 1 ≤ D3Stopped.level x.S)
    (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc j : ℕ) (hf : (soloPoly x.S).Monic) :
    let f := soloPoly x.S
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
    preWalkGen D4CoreCut.cutCoreRaw (A_fuel C K_loc) (8 * K_loc) (rankQuery x j) =
      startV2 ctx rootNode.toWorkItem B_bud (if j = 0 then 0 else j - 1) := by
  intro f D guard B_bud ctx rootNode
  obtain ⟨hpoly, _, fields, fBitsRaw_eq_polynomialBits, encodeList_mem_len_le, clog2_le_self, _,
    _, fuel_bounds⟩ := DetDLP.m14_base_fuel
  obtain ⟨_, _, _, hfield3, _, hfield5, hfield6, hfield7, _⟩ := fields x
  let q := rankQuery x j
  let A_fl := A_fuel C K_loc
  have hin_le_q : (D4Plan.input x).length ≤ q.length :=
    encodeList_mem_len_le List.mem_cons_self
  have hfb_in := fuel_bounds x K_loc (D4Plan.input x) le_rfl
  have hfb_q := fuel_bounds x K_loc q hin_le_q
  have hfBits_eq : fBitsRaw A_fl (D4Plan.input x) = polynomialBits f :=
    fBitsRaw_eq_polynomialBits x hL_level A_fl hfb_in.2.1 hfb_in.2.2.1
  have hfld_q0 : fld q 0 = D4Plan.input x := by
    simp [q, rankQuery, fld_encodeList_id]
  have hnum_q1 : num q 1 = j := by
    simp [q, rankQuery, num, fld_encodeList_id]
  obtain ⟨fuel, hfuel_def⟩ : ∃ fl, fl = polyUnits A_fl q := ⟨_, rfl⟩
  have hfq_len : (polyUnits A_fl q).length = fuel.length := by rw [hfuel_def]
  change preWalkGen D4CoreCut.cutCoreRaw A_fl (8 * K_loc) q = _
  unfold preWalkGen startV2
  dsimp only [letFun]
  rw [← hfuel_def, hfld_q0, hnum_q1, hfield3, hfield5, hfield6, hfield7,
      num_countWord, num_countWord, num_countWord, num_countWord, hfBits_eq,
      ← rootSoloNode_bits_eq x f (pktOKOf E_pkt o_pkt K_loc x f hf)]
  have hD_le_F : Nat.clog 32 (4 * x.m) ≤ fuel.length := by
    have hcl : Nat.clog 32 (4 * x.m) ≤ Nat.clog 2 (4 * x.m) := by
      rw [Nat.clog_pow_left 2 5 (4 * x.m)]; omega
    have h4m : 4 * x.m ≤ 4 * x.m * x.k := by
      calc 4 * x.m = 4 * x.m * 1 := (mul_one _).symm
        _ ≤ 4 * x.m * x.k := Nat.mul_le_mul_left _ x.hk
    exact (hcl.trans (clog2_le_self _)).trans (h4m.trans (hfq_len ▸ hfb_q.1))
  have hl_le_F : x.l ≤ fuel.length := by
    have h4L_pos : 1 ≤ 4 * D3Stopped.level x.S := by omega
    exact (Nat.le_mul_of_pos_right x.l h4L_pos).trans (hfq_len ▸ hfb_q.2.2.2.2.2.2.1)
  have hctx_eq : ctxRaw fuel x.S x.m x.p guard x.l (polynomialBits f) = ctx :=
    ctxRaw_eq_contextV2 fuel x.S x.m x.p guard x.l (polynomialBits f)
      hD_le_F (hfq_len ▸ hfb_q.2.2.2.2.1) hl_le_F (fun d => hfq_len ▸ hfb_q.2.2.2.1 d)
  have hone_eq : oneWordFuel fuel (x.l * (polynomialBits f).length) = oneWord ctx := by
    have hpf_len : (polynomialBits f).length = 4 * D3Stopped.level x.S := by
      unfold polynomialBits
      simp only [List.length_ofFn]
      exact (hpoly hL_level).2.1
    unfold oneWordFuel oneWord
    have hctx3 : (fld ctx 3).length = x.l := by simp [ctx, contextV2, fld_pack]
    have hctx4 : (fld ctx 4).length = (polynomialBits f).length := by simp [ctx, contextV2, fld_pack]
    rw [hctx3, hctx4, rangeFuel_eq fuel _ (by rw [hpf_len]; exact hfq_len ▸ hfb_q.2.2.2.2.2.2.1)]
  rw [hctx_eq, hone_eq]

private theorem mkPlanBranchAux_none {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc guard B_bud : ℕ)
    (certTree : D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard))
    (hvalid : treeAll SoloLeafData.Valid certTree)
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
      HitDegProp x hbLen doneNodes hperm)
    (u : Fin (2 ^ B_bud)) (hnone : certTree.read B_bud u.val = none) :
    mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all u =
      let L := x.spec.lookupVerts
      let lfFn := missLeafFn x hbLen
      let H := D4CoreCut.reattach x.G L (4 * x.m) lfFn
      ⟨4 * x.m, lfFn, 0,
        fun _ => emptyStoppedDescRaw x.desc (polynomialBits f) x.S x.p x.l,
        fun j β => (emptyStoppedSpec x f (H.deg (Fin.natAdd L.card j))).value hf x.A (guard + x.p) β⟩ := by
  unfold mkPlanBranchAux
  dsimp only
  split
  · rfl
  · rename_i lf hsome
    rw [hnone] at hsome
    cases hsome

private theorem mkPlanBranchAux_some {C c : ℕ} (x : Input C c) {f : ℤ[X]} (hf : f.Monic)
    (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc guard B_bud : ℕ)
    (certTree : D4RankCode.Tree (SoloLeafData x hf E_pkt o_pkt K_loc guard))
    (hvalid : treeAll SoloLeafData.Valid certTree)
    (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
    (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
      (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
      HitDegProp x hbLen doneNodes hperm)
    (u : Fin (2 ^ B_bud)) (lf : SoloLeafData x hf E_pkt o_pkt K_loc guard)
    (hsome : certTree.read B_bud u.val = some lf) :
    mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all u =
      let hlf : lf.Valid := treeAll_read hvalid B_bud u.val hsome
      let lfFn := hitLeafFn x hbLen lf.doneNodes hlf.2.2.2
      ⟨lf.doneNodes.length, lfFn, lf.weight,
        fun j =>
          let nd := lf.doneNodes.get j
          stoppedDesc x.desc x.S x.l nd.pCurr nd.d f nd.G nd.toStoppedSpec.tableBits,
        fun j β =>
          let nd := lf.doneNodes.get j
          let hdeg := hdeg_all lf.doneNodes hlf.2.2.2 j
          nd.toStoppedSpec.value hf x.A (guard + x.p) (fun kp => β (kp.cast hdeg.symm))⟩ := by
  unfold mkPlanBranchAux
  dsimp only
  split
  · rename_i hnone
    rw [hsome] at hnone
    cases hnone
  · rename_i lf' hsome'
    have heq : lf' = lf := Option.some.inj (hsome'.symm.trans hsome)
    subst heq
    rfl

end WireEqualities

end

end DetDLP.M14EnumWireInternal

open DetDLP.M14EnumWireInternal in
theorem solution :
    (∀ (O : PrimitiveMachine) (o : Fin O.tapeCount)
        (pre post : Wd → Wd) (_hp : PolyT pre) (_hq : PolyT post),
        ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
          1 ≤ K ∧
          ∀ (q ans : Wd) (τ σ : ℝ) (M_len : ℕ),
            0 ≤ τ → 0 ≤ σ → ans ≠ [] →
            RunsWithin O o (pre q) ans τ σ →
            (callPair q []).length ≤ M_len →
            (callPair q (pre q)).length ≤ M_len →
            (callPair q ans).length ≤ M_len →
            ans.length ≤ M_len →
            (post (pack [q, ans])).length ≤ M_len →
            RunsWithin M out q (post (pack [q, ans]))
              (2 * (polyBound K M_len + (K : ℝ) * (τ + σ + 1)))
              (polyBound K M_len + (K : ℝ) * (σ + 1))) ∧
    (∀ {C c : ℕ} (x : Input C c) (n : ℕ)
        (leafFn : D4CoreCut.B x.G x.spec.lookupVerts → Fin n) (degF l qPrec : ℕ),
        let w_re := getReattachWit x n leafFn
        lookupDescsRaw x.desc (D4Slice.field 8 (D4Plan.input x)) degF l qPrec =
          List.ofFn (fun v : Fin x.spec.lookupVerts.card =>
            lookupDesc x.desc (w_re.old v).val.val degF l qPrec)) ∧
    (∀ {C c : ℕ} (x : Input C c) {f : ℤ[X]} {PktOK : PktPred f x.l}
        (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
        (doneNodes : List (SoloNode x f PktOK))
        (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k)))
        (bi : Fin (4 * x.m * x.k)),
        findBoundaryLeaf (doneNodes.map (·.toWorkItem.bits)) bi.val =
          (hitLeafFn x hbLen doneNodes hperm (bi.cast hbLen.symm)).val) ∧
    (∀ {C c : ℕ} (x : Input C c) (_hL_level : 1 ≤ D3Stopped.level x.S)
        (E_pkt : PrimitiveMachine) (o_pkt : Fin E_pkt.tapeCount) (K_loc j : ℕ) (hf : (soloPoly x.S).Monic),
        let f := soloPoly x.S
        let D := Nat.clog 32 (4 * x.m)
        let guard := totalGuard x.S D
        let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
        let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
        let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
        preWalkGen D4CoreCut.cutCoreRaw (A_fuel C K_loc) (8 * K_loc) (rankQuery x j) =
          startV2 ctx rootNode.toWorkItem B_bud (if j = 0 then 0 else j - 1)) ∧
    (∀ {C c : ℕ} (x : Input C c) (_hL_level : 1 ≤ D3Stopped.level x.S)
        (M_node E_pkt : PrimitiveMachine) (o_node : Fin M_node.tapeCount) (o_pkt : Fin E_pkt.tapeCount)
        (K_loc H_loc c_loc : ℕ)
        (hf : (soloPoly x.S).Monic)
        (hdeg_f : (soloPoly x.S).natDegree = 4 * Nat.clog 2 x.S)
        (hpos : 0 < (soloPoly x.S).natDegree),
    let f := soloPoly x.S
    let D := Nat.clog 32 (4 * x.m)
    let guard := totalGuard x.S D
    let B_bud := D4UnrollBudget.budget x.S D (8 * K_loc)
    let rootNode := rootSoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)
    ∀ (rootUnroll : SoloUnroll x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc D rootNode),
    let certTree := unrollCertFuel x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc guard (64 ^ D)
      [⟨D, rootNode, rootUnroll⟩] [] 1 0
    ∀ (hvalid : treeAll SoloLeafData.Valid certTree)
        (hbLen : (D4CoreCut.boundaryEdges x.G x.spec.lookupVerts).length = 4 * x.m * x.k)
        (hdeg_all : ∀ (doneNodes : List (SoloNode x f (pktOKOf E_pkt o_pkt K_loc x f hf)))
          (hperm : List.Perm (pinFirsts doneNodes) (List.finRange (4 * x.m * x.k))),
          HitDegProp x hbLen doneNodes hperm),
    let br := mkPlanBranchAux x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all
    ∀ (hverts : ∀ u : Fin (2 ^ B_bud),
          (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).nV ≤
            4 * x.m + 64 ^ Nat.clog 32 (4 * x.m))
        (hdegree : ∀ u : Fin (2 ^ B_bud),
          (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn).maxDeg * x.m ≤
            1217 * (C + 1) ^ 3 * x.b)
        (hcorrect :
          answer x = encodeNatListBin (List.ofFn fun j : Fin x.l =>
            word f x.l (guard + x.p) hf
              (∑ u : Fin (2 ^ B_bud), (br u).wVal *
                BTNContract (D4CoreCut.reattach x.G x.spec.lookupVerts (br u).n (br u).leafFn)
                  (planVOfBr x f guard B_bud br u))
              j ⟨0, hpos⟩ / 2 ^ guard)),
    let P := mkSoloPlanFromBr x f hf hdeg_f hpos guard B_bud br hverts hdegree hcorrect
    let ctx := contextV2 x.S x.m x.p guard x.l (polynomialBits f)
    let F := soloStepFn M_node o_node ctx
    (∀ walkerOut : Wd,
      postWalkGen D4CoreCut.reattachRaw (A_fuel C K_loc) (8 * K_loc)
        (pack [rankQuery x 0, walkerOut]) = header P) ∧
    (∀ u : Fin P.N,
      let walkerOut := tag ((unrollRankTreeV2 ctx rootNode.toWorkItem F).read B_bud u.val)
      postWalkGen D4CoreCut.reattachRaw (A_fuel C K_loc) (8 * K_loc)
        (pack [rankQuery x (u.val + 1), walkerOut]) = branch P u)) := by
  refine ⟨soloOneCall, @lookupDescsRaw_eq, @findBoundaryLeaf_eq_hitLeafFn, @preWalkGen_eq_startV2, ?_⟩
  intro C c x hL_level M_node E_pkt o_node o_pkt K_loc H_loc c_loc hf hdeg_f hpos
    f D guard B_bud rootNode rootUnroll certTree hvalid hbLen hdeg_all br hverts hdegree hcorrect P ctx F
  obtain ⟨hpoly, _, fields, fBitsRaw_eq_polynomialBits, encodeList_mem_len_le, _, _, _, fuel_bounds⟩ :=
    DetDLP.m14_base_fuel
  obtain ⟨hfield0, _, _, hfield3, hfield4, hfield5, hfield6, hfield7, _⟩ := fields x
  constructor
  · intro walkerOut
    let pairW := pack [rankQuery x 0, walkerOut]
    have hin_le : (D4Plan.input x).length ≤ pairW.length :=
      (encodeList_mem_len_le (w := D4Plan.input x) List.mem_cons_self).trans
        (encodeList_mem_len_le (w := rankQuery x 0) List.mem_cons_self)
    have hfb_in := fuel_bounds x K_loc (D4Plan.input x) le_rfl
    have hfb_pw := fuel_bounds x K_loc pairW hin_le
    have hfBits_eq : fBitsRaw (A_fuel C K_loc) (D4Plan.input x) = polynomialBits (soloPoly x.S) :=
      fBitsRaw_eq_polynomialBits x hL_level (A_fuel C K_loc) hfb_in.2.1 hfb_in.2.2.1
    unfold postWalkGen
    dsimp only [letFun]
    have hfld0 : fld pairW 0 = rankQuery x 0 := by simp [pairW, fld_pack]
    have hinp0 : fld (rankQuery x 0) 0 = D4Plan.input x := by simp [rankQuery, fld_encodeList_id]
    have hj0 : num (rankQuery x 0) 1 = 0 := by simp [rankQuery, num, fld_encodeList_id]
    rw [hfld0, hinp0, hj0, if_pos rfl, hfield3, hfield5,
        num_countWord, num_countWord, hfBits_eq,
        unaryFuelRep_eq (polyUnits (A_fuel C K_loc) pairW) _ false hfb_pw.2.2.2.2.2.1]
    unfold header
    dsimp only [P, mkSoloPlanFromBr]
    rw [countWord_two_pow]
    rfl
  · intro u walkerOut
    let pairW := pack [rankQuery x (u.val + 1), walkerOut]
    obtain ⟨fuel, hfuel_def⟩ : ∃ fl, fl = polyUnits (A_fuel C K_loc) pairW := ⟨_, rfl⟩
    have hfpw_len : (polyUnits (A_fuel C K_loc) pairW).length = fuel.length := by rw [hfuel_def]
    have hin_le : (D4Plan.input x).length ≤ pairW.length :=
      (encodeList_mem_len_le (w := D4Plan.input x) List.mem_cons_self).trans
        (encodeList_mem_len_le (w := rankQuery x (u.val + 1)) List.mem_cons_self)
    have hfb_in := fuel_bounds x K_loc (D4Plan.input x) le_rfl
    have hfb_pw := fuel_bounds x K_loc pairW hin_le
    obtain ⟨f_poly, hf_def⟩ : ∃ g, g = f := ⟨_, rfl⟩
    have hf_mon : f_poly.Monic := hf_def ▸ hf
    have hfBits_eq : fBitsRaw (A_fuel C K_loc) (D4Plan.input x) = polynomialBits f_poly := by
      rw [hf_def]
      exact fBitsRaw_eq_polynomialBits x hL_level (A_fuel C K_loc) hfb_in.2.1 hfb_in.2.2.1
    have hdeg_poly : f_poly.natDegree = 4 * D3Stopped.level x.S := hf_def ▸ hdeg_f
    have hpf_len : (polynomialBits f_poly).length = f_poly.natDegree := by simp [polynomialBits]
    have hRing : RingOK f := (hpoly hL_level).2.2
    have hslots : D4GuardTree.slots D ≤ 64 ^ D := slots_bound_64 D
    have hnum_ctx0 : num ctx 0 = D := by
      dsimp only [ctx, D]; simp [contextV2, num, fld_pack]
    have hone_ctx : oneWord ctx = residue f x.l (guard + x.p) hf 1 :=
      oneWord_eq_residue_one x.S x.m x.p guard x.l f hf x.hl hpos (Nat.add_pos_right _ x.hp)
    have htree_eq : unrollRankTreeV2 ctx rootNode.toWorkItem F = treeMap (SoloLeafData.toBits ctx) certTree := by
      unfold unrollRankTreeV2
      rw [hnum_ctx0, hone_ctx]
      exact ((DetDLP.m14_sync x hf M_node E_pkt o_node o_pkt K_loc H_loc c_loc).1 hRing
        (64 ^ D) [⟨D, rootNode, rootUnroll⟩] [] 1 0 (by simpa [remSlots] using hslots)).symm
    let u' : Fin (2 ^ B_bud) := u
    have hwo_eq : walkerOut = tag ((certTree.read B_bud u'.val).map (SoloLeafData.toBits ctx)) := by
      dsimp only [walkerOut, u']
      rw [htree_eq, treeMap_read]
    have hfld0 : fld pairW 0 = rankQuery x (u'.val + 1) := by simp [pairW, u', fld_pack]
    have hfld1 : fld pairW 1 = walkerOut := by simp [pairW, fld_pack]
    have hinp0 : fld (rankQuery x (u'.val + 1)) 0 = D4Plan.input x := by simp [rankQuery, fld_encodeList_id]
    have hj_succ : num (rankQuery x (u'.val + 1)) 1 = u'.val + 1 := by
      simp [rankQuery, num, fld_encodeList_id]
    change postWalkGen D4CoreCut.reattachRaw (A_fuel C K_loc) (8 * K_loc) pairW = branch P u
    unfold postWalkGen
    dsimp only [letFun]
    rw [← hfuel_def, hfld0, hfld1, hinp0, hj_succ, if_neg (Nat.succ_ne_zero u'.val),
        hfield0, hfield3, hfield4, hfield5,
        hfield6, hfield7,
        num_countWord, num_countWord, num_countWord, num_countWord, num_countWord, hfBits_eq]
    change (if walkerOut.headD false = true then
        hitBranchRaw D4CoreCut.reattachRaw fuel (D4Plan.input x) x.desc
          (D4Slice.field 8 (D4Plan.input x)) (polynomialBits f_poly) walkerOut.tail x.m x.k x.S x.l (guard + x.p)
      else
        missBranchRaw D4CoreCut.reattachRaw fuel (D4Plan.input x) x.desc
          (D4Slice.field 8 (D4Plan.input x)) (polynomialBits f_poly) x.m x.k x.S x.p x.l (guard + x.p)) = branch P u
    let L := x.spec.lookupVerts
    let qPrec := guard + x.p
    let branchData := br u'
    have hbranch_def : branch P u =
        pack [(D4CoreCut.reattach x.G L branchData.n branchData.leafFn).encode,
          residue f x.l qPrec hf branchData.wVal,
          pack (List.ofFn (fun v : Fin L.card =>
              lookupDesc x.desc ((getReattachWit x branchData.n branchData.leafFn).old v).val.val f.natDegree x.l qPrec) ++
            List.ofFn branchData.rightSrc)] := by
      unfold branch
      have hsrc : List.ofFn (P.source u) =
          List.ofFn (fun v : Fin L.card =>
            lookupDesc x.desc ((getReattachWit x branchData.n branchData.leafFn).old v).val.val f.natDegree x.l qPrec) ++
          List.ofFn branchData.rightSrc := by
        change List.ofFn (Fin.addCases
          (fun v => lookupDesc x.desc ((getReattachWit x branchData.n branchData.leafFn).old v).val.val f.natDegree x.l qPrec)
          branchData.rightSrc) = _
        exact fin_addCases_ofFn _ _
      rw [hsrc]
      rfl
    rw [hbranch_def]
    dsimp only [branchData, br]
    cases hread : certTree.read B_bud u'.val with
    | none =>
      rw [hread] at hwo_eq
      have hhead : walkerOut.headD false = false := by rw [hwo_eq]; rfl
      rw [hhead, if_neg Bool.false_ne_true,
          mkPlanBranchAux_none x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all u' hread]
      dsimp only
      unfold missBranchRaw
      dsimp only [letFun]
      have h4m_le : 4 * x.m ≤ fuel.length := by
        have : 4 * x.m ≤ 4 * x.m * x.k := by
          calc 4 * x.m = 4 * x.m * 1 := (mul_one _).symm
            _ ≤ 4 * x.m * x.k := Nat.mul_le_mul_left _ x.hk
        exact this.trans (hfpw_len ▸ hfb_pw.1)
      have hlf_len : x.l * (polynomialBits f_poly).length ≤ fuel.length := by
        rw [hpf_len, hdeg_poly]; exact hfpw_len ▸ hfb_pw.2.2.2.2.2.2.1
      rw [rangeFuel_eq fuel (4 * x.m) h4m_le,
          rangeFuel_eq fuel (4 * x.m * x.k) (hfpw_len ▸ hfb_pw.1),
          rangeFuel_eq fuel (x.l * (polynomialBits f_poly).length) hlf_len,
          hpf_len,
          lookupDescsRaw_eq x (4 * x.m) (missLeafFn x hbLen) f_poly.natDegree x.l qPrec]
      have hrep : (List.range (4 * x.m)).map (fun _ => true) = List.replicate (4 * x.m) true :=
        List.ext_getElem (by simp) (fun _ _ _ => by simp)
      have hbmap : (List.range (4 * x.m * x.k)).map (· / x.k) =
          List.ofFn (fun i : D4CoreCut.B x.G L => (missLeafFn x hbLen i).val) := by
        apply List.ext_getElem
        · simp only [List.length_map, List.length_range, List.length_ofFn]; exact hbLen.symm
        · intro idx h1 h2; simp [missLeafFn]
      have hR_eq : D4CoreCut.reattachRaw
          (pack [D4Plan.input x, (List.range (4 * x.m)).map (fun _ => true),
            encodeNatListBin ((List.range (4 * x.m * x.k)).map (· / x.k))]) =
          (D4CoreCut.reattach x.G L (4 * x.m) (missLeafFn x hbLen)).encode := by
        rw [hrep, hbmap]
        exact (DetDLP.d4_reattach_poly_and_spec.2 x (4 * x.m) (missLeafFn x hbLen)).1
      have hzero_eq : encodeNatListBin ((List.range (x.l * f_poly.natDegree)).map fun _ => 0) =
          residue f x.l qPrec hf 0 := by
        rw [residue_zero_eq_encode f_poly x.l qPrec hf_mon]
        subst hf_def
        rfl
      have hsDescs : (List.range (4 * x.m)).map
          (fun _ => emptyStoppedDescRaw x.desc (polynomialBits f_poly) x.S x.p x.l) =
          List.ofFn (fun _ : Fin (4 * x.m) => emptyStoppedDescRaw x.desc (polynomialBits f) x.S x.p x.l) := by
        subst hf_def
        exact List.ext_getElem (by simp) (fun _ _ _ => by simp only [List.getElem_map, List.getElem_ofFn])
      rw [hR_eq, hzero_eq, hsDescs]
      subst hf_def
      rfl
    | some lf =>
      rw [hread] at hwo_eq
      have hlf : lf.Valid := treeAll_read hvalid B_bud u'.val hread
      have hhead : walkerOut.headD false = true := by rw [hwo_eq]; rfl
      have htail : walkerOut.tail = SoloLeafData.toBits ctx lf := by rw [hwo_eq]; rfl
      rw [hhead, if_pos rfl, htail,
          mkPlanBranchAux_some x hf E_pkt o_pkt K_loc guard B_bud certTree hvalid hbLen hdeg_all u' lf hread]
      dsimp only
      unfold hitBranchRaw SoloLeafData.toBits
      simp only [fld_pack, unpack_pack, List.getD_cons_zero, List.getD_cons_succ]
      rw [rangeFuel_eq fuel (4 * x.m * x.k) (hfpw_len ▸ hfb_pw.1), hpf_len,
          lookupDescsRaw_eq x lf.doneNodes.length (hitLeafFn x hbLen lf.doneNodes hlf.2.2.2) f_poly.natDegree x.l qPrec]
      have hrep : (lf.doneNodes.map (·.toWorkItem.bits)).map (fun _ => true) =
          List.replicate lf.doneNodes.length true :=
        List.ext_getElem (by simp) (fun _ _ _ => by simp)
      have hleaf_list : (List.range (4 * x.m * x.k)).map
          (findBoundaryLeaf (lf.doneNodes.map (·.toWorkItem.bits))) =
          List.ofFn (fun i : D4CoreCut.B x.G L => (hitLeafFn x hbLen lf.doneNodes hlf.2.2.2 i).val) := by
        apply List.ext_getElem
        · simp only [List.length_map, List.length_range, List.length_ofFn]; exact hbLen.symm
        · intro idx h1 h2
          simp only [List.length_map, List.length_range] at h1
          simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
          simpa using findBoundaryLeaf_eq_hitLeafFn x hbLen lf.doneNodes hlf.2.2.2 ⟨idx, h1⟩
      have hR_eq : D4CoreCut.reattachRaw
          (pack [D4Plan.input x, (lf.doneNodes.map (·.toWorkItem.bits)).map (fun _ => true),
            encodeNatListBin ((List.range (4 * x.m * x.k)).map
              (findBoundaryLeaf (lf.doneNodes.map (·.toWorkItem.bits))))]) =
          (D4CoreCut.reattach x.G L lf.doneNodes.length (hitLeafFn x hbLen lf.doneNodes hlf.2.2.2)).encode := by
        rw [hrep, hleaf_list]
        exact (DetDLP.d4_reattach_poly_and_spec.2 x lf.doneNodes.length (hitLeafFn x hbLen lf.doneNodes hlf.2.2.2)).1
      have hwt_eq : finishWt ctx (residue f x.l (guard + x.p) hf lf.accVal) lf.lossSum =
          residue f x.l qPrec hf lf.weight :=
        finishWt_eq_residue_shift x.S x.m x.p guard x.l lf.lossSum f hf hlf.1 _ lf.accVal rfl
      have hsDescs : (lf.doneNodes.map (·.toWorkItem.bits)).map
          (stoppedItemDescRaw fuel x.desc (polynomialBits f_poly) x.S x.l) =
          List.ofFn (fun j : Fin lf.doneNodes.length =>
            let nd := lf.doneNodes.get j
            stoppedDesc x.desc x.S x.l nd.pCurr nd.d f nd.G nd.toStoppedSpec.tableBits) := by
        subst hf_def
        apply List.ext_getElem
        · simp
        · intro idx h1 h2
          simp only [List.length_map] at h1
          simp only [List.getElem_map, List.getElem_ofFn]
          exact SoloNode.toStoppedSpec_desc_eq fuel (lf.doneNodes.get ⟨idx, h1⟩) (hfpw_len ▸ hfb_pw.2.2.2.2.2.2.2)
      rw [hR_eq, hwt_eq, hsDescs]
      subst hf_def
      rfl
