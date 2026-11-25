-- Prove2me | solution 1 for DetDLP.s8m_ec_pair_layout_wired_encode
-- status  : ACCEPTED   (disprove)
-- author  : @Bingsheng
-- created : 2026-11-25T03:17:37.078934+00:00
-- url     : https://prove2.me/submissions/6cb0ba32-1189-4b8e-af8d-d60f54c4c471

import Definitions.Def_DetDLP_S8M_ECPairGraph
import Definitions.Def_DetDLP_S8M_ECPairPacket
import Definitions.Def_DetDLP_S8C_TagSpec
import Definitions.Def_DetDLP_S8C_AddLayout
import Definitions.Def_DetDLP_S8G_FpMomentPoly

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem DetDLP.gadget_laws : DetDLP.S8C.GadgetLaws := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · -- Conjunct 1: Modular addition wrap-bit parsimony
    intro q x y z γ ssum hx hy hz
    constructor
    · rintro ⟨rfl, hsum⟩
      have hmod : z = (x + y) % q := by
        rw [← hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
      have hγ : γ = decide (q ≤ x + y) := by
        cases γ with
        | false =>
          rw [if_neg Bool.false_ne_true, zero_mul, add_zero] at hsum
          symm
          rw [decide_eq_false_iff_not]
          omega
        | true =>
          rw [if_pos rfl, one_mul] at hsum
          symm
          rw [decide_eq_true_eq]
          omega
      exact ⟨hmod, hγ, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨rfl, ?_⟩
      by_cases hq : q ≤ x + y
      · rw [decide_eq_true hq, if_pos rfl, one_mul]
        have hdiv : (x + y) / q = 1 := by
          have h1 : 1 * q ≤ x + y := by omega
          have h2 : x + y < (1 + 1) * q := by omega
          exact Nat.div_eq_of_lt_le h1 h2
        have hdm := Nat.mod_add_div (x + y) q
        rw [hdiv, mul_one] at hdm
        exact hdm
      · rw [decide_eq_false hq, if_neg Bool.false_ne_true, zero_mul, add_zero]
        exact Nat.mod_eq_of_lt (by omega)
  · -- Conjunct 2: Euclidean modular multiplication parsimony
    intro q x y z θ u₁ u₂ hx hy hz
    have hq_pos : 0 < q := by omega
    constructor
    · rintro ⟨rfl, rfl, hsum⟩
      have hz_eq : z = (x * y) % q := by
        rw [← hsum, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
      have hθ_eq : θ = (x * y) / q := by
        rw [← hsum, add_comm, Nat.add_mul_div_right _ _ hq_pos,
          Nat.div_eq_zero_iff.mpr (Or.inr hz), zero_add]
      have hθ_lt : θ < q := by
        by_contra hge
        have hq_le : q ≤ θ := Nat.le_of_not_lt hge
        have h1 : q * q ≤ θ * q := Nat.mul_le_mul_right q hq_le
        have h2 : x * y < q * q := Nat.mul_lt_mul'' hx hy
        omega
      refine ⟨hz_eq, hθ_eq, hθ_lt, rfl, ?_⟩
      rw [← hθ_eq]
    · rintro ⟨hz_eq, hθ_eq, _, rfl, rfl⟩
      refine ⟨rfl, by rw [hθ_eq], ?_⟩
      rw [hz_eq, mul_comm ((x * y) / q) q, Nat.div_add_mod]
  · -- Conjunct 3: Prime-field zero-indicator parsimony
    intro p _ u ζ winv
    cases ζ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, sub_zero, one_mul, true_and,
        false_eq_decide_iff]
      constructor
      · intro hmul
        have hu : u ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hmul
          exact zero_ne_one hmul
        refine ⟨hu, ?_⟩
        calc winv = u⁻¹ * (u * winv) := (inv_mul_cancel_left₀ hu winv).symm
          _ = u⁻¹ := by rw [hmul, mul_one]
      · rintro ⟨hu, rfl⟩
        exact mul_inv_cancel₀ hu
    | true =>
      simp only [↓reduceIte, one_mul, sub_self, zero_mul, and_true, true_eq_decide_iff]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, inv_zero.symm⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, inv_zero⟩
  · -- Conjunct 4.1: 5-branch partition of unity
    intro ι₁ ι₂ ζx ζy
    cases ι₁ <;> cases ι₂ <;> cases ζx <;> cases ζy <;> decide
  · -- Conjunct 4.2: Short-Weierstrass gated slope uniqueness
    intro p _ _hp2 aE bE x₁ y₁ x₂ y₂ lsl ι₁ ι₂ heq1 heq2
    dsimp only
    cases ι₁ with
    | true =>
      simp
    | false =>
      cases ι₂ with
      | true =>
        simp
      | false =>
        by_cases hdx : x₂ - x₁ = 0
        · have hζx : decide (x₂ - x₁ = 0) = true := decide_eq_true hdx
          rw [hζx]
          by_cases hsy : y₁ + y₂ = 0
          · have hζy : decide (y₁ + y₂ = 0) = true := decide_eq_true hsy
            rw [hζy]
            simp
          · have hζy : decide (y₁ + y₂ = 0) = false := decide_eq_false hsy
            rw [hζy]
            simp only [Bool.false_eq_true, Bool.not_false, Bool.not_true, Bool.and_self,
              Bool.and_false, ↓reduceIte, sub_zero, one_mul, sub_self, mul_zero, zero_mul,
              true_and, and_true]
            have hx_eq : x₂ = x₁ := sub_eq_zero.mp hdx
            have hy_sq : y₁ ^ 2 = y₂ ^ 2 := by
              rw [heq1, heq2, hx_eq]
            have hfac : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination hy_sq
            have hy_eq : y₁ = y₂ :=
              sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hsy)
            have h2y_ne : 2 * y₁ ≠ 0 := by
              rw [two_mul]
              intro h0
              apply hsy
              rw [← hy_eq]
              exact h0
            constructor
            · intro hlin
              have hmul : 2 * y₁ * lsl = 3 * x₁ ^ 2 + aE := sub_eq_zero.mp hlin
              calc lsl = lsl * (2 * y₁) * (2 * y₁)⁻¹ := by
                    rw [mul_assoc, mul_inv_cancel₀ h2y_ne, mul_one]
                _ = (2 * y₁ * lsl) * (2 * y₁)⁻¹ := by rw [mul_comm lsl (2 * y₁)]
                _ = (3 * x₁ ^ 2 + aE) * (2 * y₁)⁻¹ := by rw [hmul]
            · rintro rfl
              have hmul : 2 * y₁ * ((3 * x₁ ^ 2 + aE) * (2 * y₁)⁻¹) = 3 * x₁ ^ 2 + aE := by
                rw [mul_comm (3 * x₁ ^ 2 + aE) _, mul_inv_cancel_left₀ h2y_ne]
              rw [hmul, sub_self]
        · have hζx : decide (x₂ - x₁ = 0) = false := decide_eq_false hdx
          rw [hζx]
          simp only [Bool.false_eq_true, Bool.not_false, Bool.and_self, ↓reduceIte, sub_zero,
            one_mul, mul_zero, zero_mul, sub_self, and_self, and_true]
          constructor
          · intro hlin
            have hmul : (x₂ - x₁) * lsl = y₂ - y₁ := sub_eq_zero.mp hlin
            calc lsl = lsl * (x₂ - x₁) * (x₂ - x₁)⁻¹ := by
                  rw [mul_assoc, mul_inv_cancel₀ hdx, mul_one]
              _ = ((x₂ - x₁) * lsl) * (x₂ - x₁)⁻¹ := by rw [mul_comm lsl _]
              _ = (y₂ - y₁) * (x₂ - x₁)⁻¹ := by rw [hmul]
          · rintro rfl
            have hmul : (x₂ - x₁) * ((y₂ - y₁) * (x₂ - x₁)⁻¹) = y₂ - y₁ := by
              rw [mul_comm (y₂ - y₁) _, mul_inv_cancel_left₀ hdx]
            rw [hmul, sub_self]


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
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine ⟨?_⟩
  rw [curve5_Δ_eq, isUnit_iff_exists_inv]
  exact ⟨(4 : ZMod 5), four_mul_four_zmod5⟩

def zeroSeed : ECSeed 5 (blockCount (bitLen 5)) :=
  fun _ _ => ((0 : Fin 4), (0 : Fin 5))

theorem solution :
    ¬ ∀ (h : S8C.GadgetLaws)
        (a : Addresses) (ha : a.Uniform) (p : ℕ) [Fact p.Prime] (hp : 3 < p)
        (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
        (T : ℕ) (S : ECSeed p (blockCount (bitLen p))) (X : E.toAffine.Point) (η : List Bool)
        (hT : T ≤ p) (hη : η.length ≤ 2 * blockCount (bitLen p) * (2 * bitLen p + 1))
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
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let E₀ : WeierstrassCurve (ZMod 5) := ⟨0, 0, 0, 1, 1⟩
  haveI : E₀.IsElliptic := curve5_isElliptic
  let X₀ : E₀.toAffine.Point := 0
  have hp3 : 3 < 5 := by decide
  have hT : (0 : ℕ) ≤ 5 := Nat.zero_le _
  have hη : ([] : List Bool).length ≤ 2 * blockCount (bitLen 5) * (2 * bitLen 5 + 1) := Nat.zero_le _
  have hex :=
    h DetDLP.gadget_laws counterAddr counterAddr_uniform 5 hp3 E₀ 0 zeroSeed X₀ ([] : List Bool)
      hT hη (layout 1) (test true)
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
