-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxDs3.tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:40:02.216393+00:00
-- url     : https://prove2.me/submissions/991710e1-a65f-4ade-a3be-950e6d09d726

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JDomBoundOfNnMaj
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselDomainMeasurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxDs3_tags_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_W_mid_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_bound_scaled


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxDs3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxDs3
theorem _root_.solution {F : Mat k r → E} {A c K ε : ℝ} {m : ℕ} (h : CCle A m F c) (hc : 0 ≤ c) (hK : 1 ≤ K)
    (φ ψ : Bool × Mat k r → Bool × Mat k r) :
    ∀ (w pre : List (Bool × Mat k r)), (∀ x ∈ pre, inLie k r x.2 ∧ ‖x.2‖ ≤ K) →
      (∀ x ∈ w, (φ x).1 = x.1 ∧ (ψ x).1 = x.1 ∧ inLie k r (φ x).2 ∧ inLie k r (ψ x).2 ∧
        ‖(φ x).2‖ ≤ K ∧ ‖(ψ x).2‖ ≤ K ∧ ‖(φ x).2 - (ψ x).2‖ ≤ ε) →
      LRt ((pre ++ w).map Prod.fst) → (pre ++ w).length ≤ m → ∀ g ∈ GV k r,
      gN g ^ A * ‖W (pre ++ w.map φ) F g - W (pre ++ w.map ψ) F g‖ ≤ w.length * (K ^ m * ε * c) := by
  have hCk : ∀ n : ℕ, n ≤ m → CkOn (n : ℕ∞) (GV k r) F := by
    intro n hn g₀ hg₀
    obtain ⟨U, f', hU, hg, hcd, hfe⟩ := h.1 g₀ hg₀
    exact ⟨U, f', hU, hg, hcd.of_le (by exact_mod_cast hn), hfe⟩
  have hsubL : ∀ X Y : Mat k r, inLie k r X → inLie k r Y → inLie k r (X - Y) := by
    intro X Y hX hY
    unfold inLie at hX hY ⊢
    rw [Matrix.conjTranspose_sub, sub_mul, mul_sub]
    calc Xᴴ * Hpk k r - Yᴴ * Hpk k r + (Hpk k r * X - Hpk k r * Y)
        = (Xᴴ * Hpk k r + Hpk k r * X) - (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [hX, hY, sub_zero]
  have hpn0 : ∀ l : List (Bool × Mat k r), 0 ≤ pn l := fun l =>
    List.prod_nonneg fun a ha => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp ha; exact norm_nonneg _
  have hpnK : ∀ l : List (Bool × Mat k r), (∀ y ∈ l, ‖y.2‖ ≤ K) → pn l ≤ K ^ l.length := by
    intro l hlK
    induction l with
    | nil => simp [pn]
    | cons y l ih =>
      have h1 := hlK y (List.mem_cons_self ..)
      have h2 := ih fun z hz => hlK z (List.mem_cons_of_mem _ hz)
      have h3 : pn (y :: l) = ‖y.2‖ * pn l := by simp [pn]
      rw [h3, List.length_cons, pow_succ]
      calc ‖y.2‖ * pn l ≤ K * K ^ l.length := mul_le_mul h1 h2 (hpn0 l) (by linarith)
        _ = K ^ l.length * K := mul_comm _ _
  have hgN : ∀ g : Mat k r, 0 ≤ gN g ^ A := fun g => Real.rpow_nonneg (by unfold gN; exact Real.sqrt_nonneg _) A
  intro w
  induction w with
  | nil =>
    intro pre _ _ _ _ g _
    simp
  | cons x w ih =>
    intro pre hpre hw ht hl g hg
    obtain ⟨hφ1, hψ1, hφL, hψL, hφK, hψK, hε⟩ := hw x (List.mem_cons_self ..)
    have hw' : ∀ y ∈ w, (φ y).1 = y.1 ∧ (ψ y).1 = y.1 ∧ inLie k r (φ y).2 ∧ inLie k r (ψ y).2 ∧
        ‖(φ y).2‖ ≤ K ∧ ‖(ψ y).2‖ ≤ K ∧ ‖(φ y).2 - (ψ y).2‖ ≤ ε :=
      fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hpre' : ∀ y ∈ pre ++ [φ x], inLie k r y.2 ∧ ‖y.2‖ ≤ K := by
      intro y hy
      rcases List.mem_append.mp hy with h' | h'
      · exact hpre y h'
      · rw [List.mem_singleton] at h'; subst h'; exact ⟨hφL, hφK⟩
    have ht' : LRt ((pre ++ [φ x] ++ w).map Prod.fst) := by
      have e : (pre ++ [φ x] ++ w).map Prod.fst = (pre ++ x :: w).map Prod.fst := by simp [hφ1]
      rw [e]; exact ht
    have hl' : (pre ++ [φ x] ++ w).length ≤ m := by simpa using hl
    have ih' := ih (pre ++ [φ x]) hpre' hw' ht' hl' g hg
    have hwψ : (w.map ψ).map Prod.fst = w.map Prod.fst := tags_map ψ w fun y hy => (hw' y hy).2.1
    have hallpre : AllLie pre := fun y hy => (hpre y hy).1
    have hallq : AllLie (w.map ψ) := by
      intro y hy; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy; exact (hw' z hz).2.2.2.1
    have hlen : pre.length + 1 + w.length ≤ m := by simp at hl; omega
    have hCk' : CkOn ((pre.length + 1 + (w.map ψ).length : ℕ) : ℕ∞) (GV k r) F := by
      rw [List.length_map]; exact hCk _ hlen
    have hDL : inLie k r ((φ x).2 - (ψ x).2) := hsubL _ _ hφL hψL
    have hmid := W_mid_add (F := F) pre (w.map ψ) x.1 hallpre hallq hψL hDL hCk' g hg
    rw [add_sub_cancel] at hmid
    have hφx : φ x = (x.1, (φ x).2) := Prod.ext hφ1 rfl
    have hψx : ψ x = (x.1, (ψ x).2) := Prod.ext hψ1 rfl
    have e1 : pre ++ (x :: w).map φ = pre ++ [φ x] ++ w.map φ := by simp
    have e2 : pre ++ (x :: w).map ψ = pre ++ (x.1, (ψ x).2) :: w.map ψ := by
      rw [List.map_cons, ← hψx]
    have e3 : pre ++ [φ x] ++ w.map ψ = pre ++ (x.1, (φ x).2) :: w.map ψ := by
      rw [List.append_assoc, List.singleton_append, ← hφx]
    have hsplit : W (pre ++ (x :: w).map φ) F g - W (pre ++ (x :: w).map ψ) F g =
        (W (pre ++ [φ x] ++ w.map φ) F g - W (pre ++ [φ x] ++ w.map ψ) F g) +
          W (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) F g := by
      rw [e1, e2, e3, hmid]; abel
    have ht2 : LRt ((pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ).map Prod.fst) := by
      have e : (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ).map Prod.fst =
          (pre ++ x :: w).map Prod.fst := by
        simp only [List.map_append, List.map_cons, hwψ]
      rw [e]; exact ht
    have hall2 : AllLie (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) := by
      intro y hy
      rcases List.mem_append.mp hy with h' | h'
      · exact hallpre y h'
      · rcases List.mem_cons.mp h' with h'' | h''
        · subst h''; exact hDL
        · exact hallq y h''
    have hl2 : (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ).length ≤ m := by simpa using hl
    have hb2 := bound_scaled h _ ht2 hall2 hl2 g hg
    have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hε
    have hK0 : 0 ≤ K := by linarith
    have hpn2 : pn (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) ≤ K ^ m * ε := by
      have hpre_pn : pn pre ≤ K ^ pre.length := hpnK pre fun y hy => (hpre y hy).2
      have hq_pn : pn (w.map ψ) ≤ K ^ w.length := by
        have h5 := hpnK (w.map ψ) (by
          intro y hy; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy; exact (hw' z hz).2.2.2.2.2.1)
        simpa using h5
      have e : pn (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) =
          pn pre * (‖(φ x).2 - (ψ x).2‖ * pn (w.map ψ)) := by
        simp [pn, List.map_append, List.prod_append]
      rw [e]
      calc pn pre * (‖(φ x).2 - (ψ x).2‖ * pn (w.map ψ)) ≤ K ^ pre.length * (ε * K ^ w.length) :=
            mul_le_mul hpre_pn (mul_le_mul hε hq_pn (hpn0 _) hε0)
              (mul_nonneg (norm_nonneg _) (hpn0 _)) (pow_nonneg hK0 _)
        _ = K ^ (pre.length + w.length) * ε := by rw [pow_add]; ring
        _ ≤ K ^ m * ε := by
            apply mul_le_mul_of_nonneg_right _ hε0
            exact pow_le_pow_right₀ hK (by omega)
    rw [hsplit]
    have hg0 := hgN g
    calc gN g ^ A * ‖(W (pre ++ [φ x] ++ w.map φ) F g - W (pre ++ [φ x] ++ w.map ψ) F g) +
          W (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) F g‖
        ≤ gN g ^ A * ‖W (pre ++ [φ x] ++ w.map φ) F g - W (pre ++ [φ x] ++ w.map ψ) F g‖ +
          gN g ^ A * ‖W (pre ++ (x.1, (φ x).2 - (ψ x).2) :: w.map ψ) F g‖ := by
          rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hg0
      _ ≤ w.length * (K ^ m * ε * c) + K ^ m * ε * c :=
          add_le_add ih' (hb2.trans (by
            have := mul_le_mul_of_nonneg_right hpn2 hc
            linarith))
      _ = ((x :: w).length : ℝ) * (K ^ m * ε * c) := by push_cast [List.length_cons]; ring
end Formalism.FourierDecayAlt.P.JFxDs3
