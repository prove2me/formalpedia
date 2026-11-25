-- Prove2me | solution 1 for DetDLP.s8m_ec_pair_layout_encode
-- status  : ACCEPTED   (disprove)
-- author  : @Bingsheng
-- created : 2026-11-25T02:35:45.928831+00:00
-- url     : https://prove2.me/submissions/ba01c730-e184-4a8e-b612-84e979d3ecb5

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8M_ECPairPacket
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_S8C_AddLayout
import Definitions.Def_DetDLP_S8G_FpMomentPoly

set_option autoImplicit false
set_option maxHeartbeats 800000

open DetDLP
open DetDLP.S8C
open DetDLP.S8M.ECPair
open DetDLP.S8M.ECPair.Packet
open DetDLP.S8C.AddLayout
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open OAI.Algorithms.SubexponentialSAT.Encoding
open Groundwork
open w4_M5Network

attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f

theorem unary_zero : Unary (fun (_ : S8G.FpMoment.Code.W) => 0) :=
  PolyT.const (List.replicate 0 ())

def counterAddr : Addresses where
  nv := fun _ => 0
  ne := fun _ => 0
  src := fun _ _ => 0
  dst := fun _ _ => 0
  check := fun _ => false

theorem counterAddr_uniform : counterAddr.Uniform where
  nv := by fun_prop
  ne := by fun_prop
  vert := by unfold counterAddr; simpa using unary_zero
  edge := by unfold counterAddr; simpa using unary_zero
  src := by fun_prop
  dst := by fun_prop
  check := by fun_prop

lemma frame_append_inj' {a b as bs : List Bool}
    (h : frame a ++ as = frame b ++ bs) : a = b ∧ as = bs := by
  revert b as bs h
  induction a with
  | nil =>
    intro b as bs h
    cases b with
    | nil =>
      simp [frame] at h
      exact ⟨rfl, h⟩
    | cons xb b' =>
      simp [frame] at h
  | cons xa a ih =>
    intro b as bs h
    cases b with
    | nil =>
      simp [frame] at h
    | cons xb b' =>
      have h' : true :: xa :: (frame a ++ as) = true :: xb :: (frame b' ++ bs) := by
        simpa [frame] using h
      obtain ⟨hxb, hrest⟩ : xa = xb ∧ frame a ++ as = frame b' ++ bs := by
        injection h' with _ hmid
        injection hmid with hxb hrest
        exact ⟨hxb, hrest⟩
      obtain ⟨ha, has⟩ := ih hrest
      subst hxb ha
      exact ⟨rfl, has⟩

lemma encodeList_cons_inj {α} (enc : α → List Bool) {a b : α} {as bs : List α}
    (h : encodeList enc (a :: as) = encodeList enc (b :: bs)) :
    enc a = enc b ∧ encodeList enc as = encodeList enc bs := by
  have h' : true :: (frame (enc a) ++ encodeList enc as) =
      true :: (frame (enc b) ++ encodeList enc bs) := by
    simpa [encodeList] using h
  injection h' with _ happ
  exact frame_append_inj' happ

lemma outerPacket_graph_eq {d g₁ g₂ : List Bool} {s : ℕ}
    (h : outerPacket d g₁ s = outerPacket d g₂ s) : g₁ = g₂ := by
  simp only [outerPacket] at h
  have h1 := encodeList_cons_inj id h
  have h2 := encodeList_cons_inj id h1.2
  exact h2.1

theorem empty_packet_ne_layout1_subdiv :
    S8H.WirePacket.packet 0 0 (fun _ => 0) (fun _ => 0) ≠
      (w3_factorGraph (layout 1)).subdivision.encode := by
  intro h
  simp only [S8H.WirePacket.packet, graphPacket, BipartiteMultigraph.encode,
    WireGraph.subdivision_nE, w3_factorGraph, layout] at h
  have h1 := encodeList_cons_inj id h
  have h2 := encodeList_cons_inj id h1.2
  have hcw : countWord 0 = countWord (2 * (1 * 5)) := h2.1
  simp [countWord] at hcw
  exact absurd hcw (by decide : ([false] : List Bool) ≠ Nat.bits 10)

theorem four_mul_four_zmod5 : (4 : ZMod 5) * 4 = 1 := by decide

theorem curve5_Δ_eq :
    WeierstrassCurve.Δ (⟨0, 0, 0, 1, 1⟩ : WeierstrassCurve (ZMod 5)) = (4 : ZMod 5) := by
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  decide

theorem curve5_isElliptic :
    (⟨0, 0, 0, 1, 1⟩ : WeierstrassCurve (ZMod 5)).IsElliptic := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨?_⟩
  rw [curve5_Δ_eq, isUnit_iff_exists_inv]
  exact ⟨(4 : ZMod 5), four_mul_four_zmod5⟩

def zeroSeed : ECSeed 5 (blockCount (bitLen 5)) :=
  fun _ _ => ((0 : Fin 4), (0 : Fin 5))

theorem solution :
    ¬ ∀ (a : Addresses) (ha : a.Uniform) (p : ℕ) [Fact p.Prime]
      (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
      (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool)
      (A : w3_FactorLayout) (test : w3_factorTest A),
      ∃ (build :
          make a (word E T S X η) =
            encodeBTNInstance (word E T S X η) (w3_factorGraph A).subdivision
              (scale (blockCount (bitLen p)) (bitLen p)) (scale (blockCount (bitLen p)) (bitLen p)) 1)
        (eval :
          ∀ v a',
          port a (encodePortQuery (word E T S X η) v.val (List.ofFn a')) =
            encodeNatListBin
              [if (w3_factorGraph A).subdivisionTensor (w3_factorChecks A test) v a' then 1 else 0]),
        True := by
  intro h
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  let E₀ : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, 1, 1⟩
  have : E₀.IsElliptic := curve5_isElliptic
  let X₀ : E₀.toAffine.Point := 0
  have hex :=
    h counterAddr counterAddr_uniform 5 E₀ 0 zeroSeed X₀ ([] : List Bool) (layout 1) (test true)
  rcases hex with ⟨build, _, _⟩
  set w : List Bool := word E₀ 0 zeroSeed X₀ []
  set s : ℕ := scale (blockCount (bitLen 5)) (bitLen 5)
  have hs : sizeField w = s := sizeField_word E₀ 0 zeroSeed X₀ []
  have hmake :
      make counterAddr w =
        outerPacket w (S8H.WirePacket.packet 0 0 (fun _ => 0) (fun _ => 0)) (sizeField w) := by
    rfl
  have hbtn :
      encodeBTNInstance w (w3_factorGraph (layout 1)).subdivision s s 1 =
        outerPacket w (w3_factorGraph (layout 1)).subdivision.encode s :=
    (outerPacket_eq w (w3_factorGraph (layout 1)).subdivision s).symm
  have hpackets :
      S8H.WirePacket.packet 0 0 (fun _ => 0) (fun _ => 0) =
        (w3_factorGraph (layout 1)).subdivision.encode := by
    have houter :
        outerPacket w (S8H.WirePacket.packet 0 0 (fun _ => 0) (fun _ => 0)) s =
          outerPacket w (w3_factorGraph (layout 1)).subdivision.encode s := by
      calc
        outerPacket w (S8H.WirePacket.packet 0 0 (fun _ => 0) (fun _ => 0)) s
            = outerPacket w (S8H.WirePacket.packet 0 0 (fun _ => 0) (fun _ => 0)) (sizeField w) := by
              rw [hs]
          _ = make counterAddr w := hmake.symm
          _ = encodeBTNInstance w (w3_factorGraph (layout 1)).subdivision s s 1 := build
          _ = outerPacket w (w3_factorGraph (layout 1)).subdivision.encode s := hbtn
    exact outerPacket_graph_eq houter
  exact empty_packet_ne_layout1_subdiv hpackets
