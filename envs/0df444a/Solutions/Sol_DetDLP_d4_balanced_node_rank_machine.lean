-- Prove2me | solution 1 for DetDLP.d4_balanced_node_rank_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:42:37.79262+00:00
-- url     : https://prove2.me/submissions/dad9dab6-8fcf-44ca-ace9-ef091eb757d3

import Definitions.Def_DetDLP_D4NodeQuery
import Definitions.Def_DetDLP_W1_Pipeline
import Theorems.Thm_DetDLP_d2_terminal_greedy_correct
import Theorems.Thm_DetDLP_d2_terminal_greedy_poly
set_option autoImplicit false
open Groundwork DetDLP DetDLP.D4NodeQuery DetDLP.AppendixD4 DetDLP_W1_Queries Polynomial OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP_W1_Pipeline.WordPipeline
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk first_poly more_poly frame_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86
private theorem prepP : PolyT prepare := by
  have hd := d2_terminal_greedy_poly
  unfold prepare emit; fun_prop
private theorem prepE (G : Graph) {a u p l b : ℕ} (host : Fin b → Fin G.nV) (f : ℤ[X]) (j : ℕ) (lbl : Label a G) (hl : D2.Greedy.run (D2.input G a host) = D2.output lbl) :
    prepare (request G host a u p l f j) = Encoding.encodeList id [stepInput G a u p l f lbl,countWord j] := by
  simp only [prepare,request,first_cons,more_cons,id_eq,hl]
  have graphField : first (D2.input G a host) = G.encode := first_cons ..
  simp only [graphField,stepInput,D2.output,emit,frame_correct,Encoding.encodeList,id_eq]

theorem solution (one : AppendixD4.OneStep) : D4NodeQuery.Local := by
  obtain ⟨A,E,oa,oe,K,run⟩ := one
  obtain ⟨D,od,H,pre⟩ := PolyTBridge.polyT_listBool_runsWithin prepare prepP
  refine ⟨machine D od A,E,resultPort D od A oa,oe,K,H,A.tapeCount+D.tapeCount,?_⟩
  intro G a u p l b τ host f hf h1 hu hM hl hp hOK hpt hpad hs hτ hmult
  obtain ⟨lbl,hlabel,padded,bal⟩ := d2_terminal_greedy_correct G a b host τ (h1.trans hM) hs hτ hmult
  obtain ⟨s,order,sound,modes,count,record,pkt⟩ := run G a u p l f hf lbl h1 hu hM hl hp hOK hpt hpad padded
  refine ⟨lbl,s,order,bal,padded,sound,modes,?_,?_,pkt⟩
  · have z := pre (request G host a u p l f 0); rw [prepE _ _ _ _ _ hlabel] at z
    apply PolyTBridge.runsWithin_mono_local (DetDLP_W1_Pipeline.WordPipeline.run D od A oa z count) <;> push_cast <;> linarith [Nat.cast_nonneg (α:=ℝ) A.tapeCount,Nat.cast_nonneg (α:=ℝ) D.tapeCount]
  · intro j; have z := pre (request G host a u p l f (j.val+1)); rw [prepE _ _ _ _ _ hlabel] at z
    apply PolyTBridge.runsWithin_mono_local (DetDLP_W1_Pipeline.WordPipeline.run D od A oa z (record j)) <;> push_cast <;> linarith [Nat.cast_nonneg (α:=ℝ) A.tapeCount,Nat.cast_nonneg (α:=ℝ) D.tapeCount]
