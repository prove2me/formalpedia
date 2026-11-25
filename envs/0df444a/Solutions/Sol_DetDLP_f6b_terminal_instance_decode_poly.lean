-- Prove2me | solution 1 for DetDLP.f6b_terminal_instance_decode_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T02:48:35.53754+00:00
-- url     : https://prove2.me/submissions/adc9c2d6-7b12-4019-9564-b1a239a773b9

import Definitions.Def_DetDLP_F6B_TerminalDecode

open DetDLP OAI.Algorithms.SubexponentialSAT Groundwork DetDLP_W1_Queries
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem field_poly (n : ℕ) : PolyT (F6B.fieldAt n) := by
  induction n with
  | zero => exact first_poly PolyT.id'
  | succ n ih => exact ih.comp (more_poly PolyT.id')

private theorem arr_poly {α : Type} [Enc α] {fs : List (α → List Bool)}
    (h : ∀ f ∈ fs, PolyT f) : PolyT (fun x => Encoding.encodeList id (fs.map (fun f => f x))) := by
  induction fs with
  | nil => exact PolyT.const _
  | cons f fs ih =>
    have hh := frame_poly (h f (by simp))
    have ht := ih (fun g hg => h g (by simp [hg]))
    apply P2M_Groundwork_PolyT_cons__3a60f43a3b86 (PolyT.const true)
    exact (PolyT.append hh ht).congr (fun x => by simp [frame_correct])

private theorem all_poly : PolyT F6B.decode := by
  let g := F6B.fieldAt 1
  let v := fun x => PolyT.bval (F6B.fieldAt 0 (g x))
  let r := fun x => v x + 3
  have hg : PolyT g := field_poly 1
  have hv : PolyT v := PolyT.bval' ((field_poly 0).comp hg)
  have hr : PolyT r := PolyT.add hv (PolyT.const 3)
  have he := PolyT.bval' ((field_poly 1).comp hg)
  have hp := PolyT.bval' (field_poly 6)
  have ha := PolyT.bval' (field_poly 7)
  have hc := M13BEndpoint.pack_poly hr (w5_M6Sort.decode_poly.comp ((field_poly 3).comp hg))
  apply arr_poly (fs := [F6B.fieldAt 0, fun x => (PolyT.bval (F6B.fieldAt 1 (g x))).bits,
    fun x => (v x).bits, fun x => (PolyT.bval (F6B.fieldAt 6 x)).bits,
    fun x => (PolyT.bval (F6B.fieldAt 7 x)).bits, fun x => (r x).bits,
    fun x => (M13BEndpoint.pack (r x) (w5_M6Sort.decode (F6B.fieldAt 3 (g x)))).bits])
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact field_poly 0
  · exact PolyT.bits he
  · exact PolyT.bits hv
  · exact PolyT.bits hp
  · exact PolyT.bits ha
  · exact PolyT.bits hr
  · exact PolyT.bits hc

private theorem pack_pairs (r : ℕ) (ps : List (ℕ × ℕ)) :
    M13BEndpoint.pack r (ps.flatMap fun p => [p.1,p.2]) =
      Nat.ofDigits r (ps.flatMap fun p => [p.1,p.2]) + r^(2*ps.length) := by
  have hl : (ps.flatMap fun p => [p.1,p.2]).length = 2 * ps.length := by
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [List.flatMap_cons,ih]; omega
  simp [M13BEndpoint.pack_eq,Nat.ofDigits_append,hl]

theorem solution : Groundwork.PolyT DetDLP.F6B.decode ∧
    ∀ (desc : List Bool) (G : BipartiteMultigraph) (b m k S P0 ℓ : ℕ)
      (lookupVerts : Finset (Fin G.nV)),
      let r := G.nV + 3
      let pairs := (List.finRange G.nE).map fun e => ((G.endpoints e).1.val,(G.endpoints e).2.val)
      let code := Nat.ofDigits r (pairs.flatMap fun xy => [xy.1,xy.2]) + r^(2*pairs.length)
      DetDLP.F6B.decode (encodeTerminalBTNInstance desc G b m k S P0 ℓ lookupVerts) =
        Encoding.encodeList id [desc,G.nE.bits,G.nV.bits,P0.bits,ℓ.bits,r.bits,code.bits] := by
  refine ⟨all_poly,?_⟩
  intro desc G b m k S P0 ℓ vs r pairs code
  have hc := pack_pairs r pairs
  simp only [pairs,List.flatMap_map,Function.comp_def] at hc
  simp [F6B.decode,encodeTerminalBTNInstance,BipartiteMultigraph.encode,F6B.fieldAt,
    code,pairs,r] at * <;> first | assumption | congr 2 <;> simpa [r,List.flatMap_map,Function.comp_def] using congrArg Nat.bits hc
