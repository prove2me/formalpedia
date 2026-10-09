-- Prove2me | solution 1 for DiscreteConvex.NetworkFlows.submodular_max_flow_min_cut
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T07:54:39.61698+00:00
-- url     : https://prove2.me/submissions/150af3a5-5474-4a16-81b5-1b0173b0b8ab

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlows_FeasibleFlowMSFP1
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaPlus
import Definitions.Def_DiscreteConvex_NetworkFlows_DeltaMinus
import Definitions.Def_DiscreteConvex_NetworkFlows_UpperCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_NegLowerCapOf
import Definitions.Def_DiscreteConvex_NetworkFlows_Submodular
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerUpper
import Definitions.Def_DiscreteConvex_NetworkFlows_IsIntegerLower

set_option autoImplicit false

namespace P8c535099
open DiscreteConvex.NetworkFlows

/-! ### Integrality on `WithTop ℝ` -/

def IntW (z : WithTop ℝ) : Prop := ∀ r : ℝ, z = (r : WithTop ℝ) → ∃ n : ℤ, (n : ℝ) = r

lemma IntW_top : IntW ⊤ := by
  intro r hr; exact absurd hr.symm (WithTop.coe_ne_top)

lemma IntW_zero : IntW 0 := by
  intro r hr
  refine ⟨0, ?_⟩
  have : ((0 : ℝ) : WithTop ℝ) = (r : WithTop ℝ) := by simpa using hr
  simpa using (WithTop.coe_injective this)

lemma IntW_add {a b : WithTop ℝ} (ha : IntW a) (hb : IntW b) : IntW (a + b) := by
  intro r hr
  induction a using WithTop.recTopCoe with
  | top => simp at hr
  | coe x =>
    induction b using WithTop.recTopCoe with
    | top => simp at hr
    | coe y =>
      obtain ⟨m, hm⟩ := ha x rfl
      obtain ⟨n, hn⟩ := hb y rfl
      have h2 : x + y = r := by exact_mod_cast hr
      exact ⟨m + n, by push_cast; rw [hm, hn, h2]⟩

lemma IntW_sum {ι : Type*} (s : Finset ι) (f : ι → WithTop ℝ) (hf : ∀ i ∈ s, IntW (f i)) :
    IntW (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IntW_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact IntW_add (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

lemma IntW_min {a b : WithTop ℝ} (ha : IntW a) (hb : IntW b) : IntW (min a b) := by
  rcases min_choice a b with h | h <;> rw [h] <;> assumption

/-! ### `NegLowerToUpper` -/

lemma N_bot : NegLowerToUpper (⊥ : WithBot ℝ) = ⊤ := rfl

lemma N_coe (r : ℝ) : NegLowerToUpper (r : WithBot ℝ) = ((-r : ℝ) : WithTop ℝ) := rfl

lemma N_ge {c : WithBot ℝ} {x : ℝ} (h : c ≤ (x : WithBot ℝ)) :
    ((-x : ℝ) : WithTop ℝ) ≤ NegLowerToUpper c := by
  induction c using WithBot.recBotCoe with
  | bot => rw [N_bot]; exact le_top
  | coe r =>
    rw [N_coe]
    have : r ≤ x := WithBot.coe_le_coe.mp h
    exact WithTop.coe_le_coe.mpr (by linarith)

lemma IntW_N {c : WithBot ℝ} (h : ∀ r : ℝ, c = (r : WithBot ℝ) → ∃ n : ℤ, (n : ℝ) = r) :
    IntW (NegLowerToUpper c) := by
  induction c using WithBot.recBotCoe with
  | bot => rw [N_bot]; exact IntW_top
  | coe r =>
    rw [N_coe]
    intro s hs
    obtain ⟨n, hn⟩ := h r rfl
    have : -r = s := WithTop.coe_injective hs
    exact ⟨-n, by push_cast; rw [hn, this]⟩

lemma key_nonneg {c : WithBot ℝ} {cu : WithTop ℝ} (h : ∃ t : ℝ, c ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cu) :
    0 ≤ NegLowerToUpper c + cu := by
  obtain ⟨t, h1, h2⟩ := h
  induction c using WithBot.recBotCoe with
  | bot => rw [N_bot]; simp
  | coe r =>
    rw [N_coe]
    induction cu using WithTop.recTopCoe with
    | top => simp
    | coe s =>
      have h1' : r ≤ t := WithBot.coe_le_coe.mp h1
      have h2' : t ≤ s := WithTop.coe_le_coe.mp h2
      rw [← WithTop.coe_add]
      exact_mod_cast (by linarith : (0:ℝ) ≤ -r + s)

/-! ### Submodularity bookkeeping -/

lemma submod_add {V : Type*} [DecidableEq V] {f g : Finset V → WithTop ℝ}
    (hf : Submodular f) (hg : Submodular g) : Submodular (fun X => f X + g X) := by
  intro X Y
  have h1 := hf X Y
  have h2 := hg X Y
  show f (X ∪ Y) + g (X ∪ Y) + (f (X ∩ Y) + g (X ∩ Y)) ≤ f X + g X + (f Y + g Y)
  calc f (X ∪ Y) + g (X ∪ Y) + (f (X ∩ Y) + g (X ∩ Y))
      = (f (X ∪ Y) + f (X ∩ Y)) + (g (X ∪ Y) + g (X ∩ Y)) := add_add_add_comm _ _ _ _
    _ ≤ (f X + f Y) + (g X + g Y) := add_le_add h1 h2
    _ = f X + g X + (f Y + g Y) := add_add_add_comm _ _ _ _

lemma submod_sum {V ι : Type*} [DecidableEq V] (s : Finset ι) (F : ι → Finset V → WithTop ℝ)
    (hF : ∀ i ∈ s, Submodular (F i)) : Submodular (fun X => ∑ i ∈ s, F i X) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro X Y; simp
  | insert a s ha ih =>
    have := submod_add (hF a (Finset.mem_insert_self a s))
      (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))
    intro X Y
    simpa only [Finset.sum_insert ha] using this X Y

/-! ### The single-arc function and the arc coefficient -/

noncomputable def arcF {V A : Type*} [DecidableEq V] (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (a : A) (X : Finset V) : WithTop ℝ :=
  (if tail a ∈ X ∧ head a ∉ X then NegLowerToUpper (cLower a) else 0) +
    (if head a ∈ X ∧ tail a ∉ X then cUpper a else 0)

def dd {V A : Type*} [DecidableEq V] (tail head : A → V) (a : A) (X : Finset V) : ℝ :=
  (if tail a ∈ X then 1 else 0) - (if head a ∈ X then 1 else 0)

lemma arcF_submod {V A : Type*} [DecidableEq V] (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (a : A)
    (h : ∃ t : ℝ, cLower a ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cUpper a) :
    Submodular (arcF tail head cUpper cLower a) := by
  have key := key_nonneg h
  have key' : 0 ≤ cUpper a + NegLowerToUpper (cLower a) := by rwa [add_comm]
  intro X Y
  simp only [arcF, ge_iff_le, Finset.mem_union, Finset.mem_inter]
  by_cases h1 : tail a ∈ X <;> by_cases h2 : head a ∈ X <;> by_cases h3 : tail a ∈ Y <;>
    by_cases h4 : head a ∈ Y <;> simp [h1, h2, h3, h4] <;>
    first | exact key | exact key'

/-! ### Choosing a point between finitely many bounds -/

lemma choose_between {ι κ : Type*} (L : Finset ι) (lo : ι → ℝ) (H : Finset κ) (hi : κ → ℝ)
    (hLH : ∀ i ∈ L, ∀ j ∈ H, lo i ≤ hi j) :
    ∃ t : ℝ, (∀ i ∈ L, lo i ≤ t) ∧ (∀ j ∈ H, t ≤ hi j) ∧
      ((∃ i ∈ L, lo i = t) ∨ (∃ j ∈ H, hi j = t) ∨ t = 0) := by
  by_cases hL : L.Nonempty
  · obtain ⟨i0, hi0, hmax⟩ := L.exists_max_image lo hL
    exact ⟨lo i0, hmax, fun j hj => hLH i0 hi0 j hj, Or.inl ⟨i0, hi0, rfl⟩⟩
  · by_cases hH : H.Nonempty
    · obtain ⟨j0, hj0, hmin⟩ := H.exists_min_image hi hH
      exact ⟨hi j0, fun i hi' => absurd ⟨i, hi'⟩ hL, hmin, Or.inr (Or.inl ⟨j0, hj0, rfl⟩)⟩
    · exact ⟨0, fun i hi' => absurd ⟨i, hi'⟩ hL, fun j hj => absurd ⟨j, hj⟩ hH, Or.inr (Or.inr rfl)⟩

lemma intSum {V : Type*} (y : V → ℝ) (hy : ∀ v, ∃ n : ℤ, (n : ℝ) = y v) (X : Finset V) :
    ∃ n : ℤ, (n : ℝ) = ∑ v ∈ X, y v :=
  ⟨∑ v ∈ X, (hy v).choose, by push_cast; exact Finset.sum_congr rfl (fun v _ => (hy v).choose_spec)⟩

lemma intSub {a b : ℝ} (ha : ∃ n : ℤ, (n : ℝ) = a) (hb : ∃ n : ℤ, (n : ℝ) = b) :
    ∃ n : ℤ, (n : ℝ) = a - b := by
  obtain ⟨m, hm⟩ := ha; obtain ⟨n, hn⟩ := hb
  exact ⟨m - n, by push_cast; rw [hm, hn]⟩

/-! ### Arc elimination -/

lemma arc_elim {V A : Type*} [Fintype V] [DecidableEq V] (tail head : A → V)
    (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (a : A)
    (hbox : ∃ t : ℝ, cLower a ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cUpper a)
    (g : Finset V → WithTop ℝ) (hg : Submodular g) (y : V → ℝ)
    (hy : ∀ X : Finset V,
      ((∑ v ∈ X, y v : ℝ) : WithTop ℝ) ≤ g X + arcF tail head cUpper cLower a X) :
    ∃ t : ℝ, cLower a ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cUpper a ∧
      (∀ X : Finset V, ((∑ v ∈ X, y v + t * dd tail head a X : ℝ) : WithTop ℝ) ≤ g X) ∧
      ((∀ r : ℝ, cLower a = (r : WithBot ℝ) → ∃ n : ℤ, (n : ℝ) = r) → IntW (cUpper a) →
        (∀ X, IntW (g X)) → (∀ v, ∃ n : ℤ, (n : ℝ) = y v) → ∃ n : ℤ, (n : ℝ) = t) := by
  classical
  -- evaluations of the arc function
  have fU : ∀ X : Finset V, tail a ∈ X → head a ∉ X →
      arcF tail head cUpper cLower a X = NegLowerToUpper (cLower a) := by
    intro X h1 h2; simp [arcF, h1, h2]
  have fW : ∀ X : Finset V, head a ∈ X → tail a ∉ X →
      arcF tail head cUpper cLower a X = cUpper a := by
    intro X h1 h2; simp [arcF, h1, h2]
  have f0 : ∀ X : Finset V, (tail a ∈ X ↔ head a ∈ X) → arcF tail head cUpper cLower a X = 0 := by
    intro X h; by_cases h1 : tail a ∈ X
    · have h2 := h.mp h1; simp [arcF, h1, h2]
    · have h2 : head a ∉ X := fun h' => h1 (h.mpr h')
      simp [arcF, h1, h2]
  obtain ⟨L, hLn, hLs⟩ : ∃ L : Finset (Option (Finset V)), (none ∈ L ↔ cLower a ≠ ⊥) ∧
      ∀ Y, (some Y ∈ L ↔ (head a ∈ Y ∧ tail a ∉ Y ∧ g Y ≠ ⊤)) :=
    ⟨Finset.univ.filter
      (fun o => Option.elim o (cLower a ≠ ⊥) (fun Y => head a ∈ Y ∧ tail a ∉ Y ∧ g Y ≠ ⊤)),
      by simp, fun Y => by simp⟩
  obtain ⟨H, hHn, hHs⟩ : ∃ H : Finset (Option (Finset V)), (none ∈ H ↔ cUpper a ≠ ⊤) ∧
      ∀ X, (some X ∈ H ↔ (tail a ∈ X ∧ head a ∉ X ∧ g X ≠ ⊤)) :=
    ⟨Finset.univ.filter
      (fun o => Option.elim o (cUpper a ≠ ⊤) (fun X => tail a ∈ X ∧ head a ∉ X ∧ g X ≠ ⊤)),
      by simp, fun X => by simp⟩
  obtain ⟨loF, hlon, hlos⟩ : ∃ f : Option (Finset V) → ℝ, f none = WithBot.unbotD 0 (cLower a) ∧
      ∀ Y, f (some Y) = (∑ v ∈ Y, y v) - WithTop.untopD 0 (g Y) :=
    ⟨fun o => Option.elim o (WithBot.unbotD 0 (cLower a))
      (fun Y => (∑ v ∈ Y, y v) - WithTop.untopD 0 (g Y)), rfl, fun _ => rfl⟩
  obtain ⟨hiF, hhin, hhis⟩ : ∃ f : Option (Finset V) → ℝ, f none = WithTop.untopD 0 (cUpper a) ∧
      ∀ X, f (some X) = WithTop.untopD 0 (g X) - ∑ v ∈ X, y v :=
    ⟨fun o => Option.elim o (WithTop.untopD 0 (cUpper a))
      (fun X => WithTop.untopD 0 (g X) - ∑ v ∈ X, y v), rfl, fun _ => rfl⟩
  have compat : ∀ i ∈ L, ∀ j ∈ H, loF i ≤ hiF j := by
    obtain ⟨t0, ht01, ht02⟩ := hbox
    intro i hi j hj
    cases i with
    | none =>
      cases j with
      | none =>
        obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp (hLn.mp hi)
        obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hHn.mp hj)
        rw [← hr] at ht01; rw [← hs] at ht02
        have e1 := WithBot.coe_le_coe.mp ht01
        have e2 := WithTop.coe_le_coe.mp ht02
        rw [hlon, hhin, ← hr, ← hs, WithBot.unbotD_coe, WithTop.untopD_coe]
        linarith
      | some X =>
        obtain ⟨hX1, hX2, hX3⟩ := (hHs X).mp hj
        obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp (hLn.mp hi)
        obtain ⟨G, hG⟩ := WithTop.ne_top_iff_exists.mp hX3
        have h := hy X
        rw [fU X hX1 hX2, ← hr, ← hG, N_coe, ← WithTop.coe_add] at h
        have h' := WithTop.coe_le_coe.mp h
        rw [hlon, hhis, ← hr, ← hG, WithBot.unbotD_coe, WithTop.untopD_coe]
        linarith
    | some Y =>
      cases j with
      | none =>
        obtain ⟨hY1, hY2, hY3⟩ := (hLs Y).mp hi
        obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (hHn.mp hj)
        obtain ⟨G, hG⟩ := WithTop.ne_top_iff_exists.mp hY3
        have h := hy Y
        rw [fW Y hY1 hY2, ← hs, ← hG, ← WithTop.coe_add] at h
        have h' := WithTop.coe_le_coe.mp h
        rw [hlos, hhin, ← hs, ← hG, WithTop.untopD_coe, WithTop.untopD_coe]
        linarith
      | some X =>
        obtain ⟨hY1, hY2, hY3⟩ := (hLs Y).mp hi
        obtain ⟨hX1, hX2, hX3⟩ := (hHs X).mp hj
        obtain ⟨GY, hGY⟩ := WithTop.ne_top_iff_exists.mp hY3
        obtain ⟨GX, hGX⟩ := WithTop.ne_top_iff_exists.mp hX3
        have hu := hy (X ∪ Y)
        have hi' := hy (X ∩ Y)
        rw [f0 (X ∪ Y) (by simp [hX1, hY1]), add_zero] at hu
        rw [f0 (X ∩ Y) (by simp [hX2, hY2]), add_zero] at hi'
        have hs := hg X Y
        have hsum : ((∑ v ∈ X, y v + ∑ v ∈ Y, y v : ℝ) : WithTop ℝ) ≤ g X + g Y := by
          rw [← Finset.sum_union_inter, WithTop.coe_add]
          exact (add_le_add hu hi').trans hs
        rw [← hGX, ← hGY, ← WithTop.coe_add] at hsum
        have h' := WithTop.coe_le_coe.mp hsum
        rw [hlos, hhis, ← hGX, ← hGY, WithTop.untopD_coe, WithTop.untopD_coe]
        linarith
  obtain ⟨t, htL, htH, htw⟩ := choose_between L loF H hiF compat
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · by_cases hc : cLower a = ⊥
    · rw [hc]; exact bot_le
    · have := htL none (hLn.mpr hc)
      obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp hc
      rw [hlon, ← hr, WithBot.unbotD_coe] at this
      rw [← hr]; exact WithBot.coe_le_coe.mpr this
  · by_cases hc : cUpper a = ⊤
    · rw [hc]; exact le_top
    · have := htH none (hHn.mpr hc)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hc
      rw [hhin, ← hr, WithTop.untopD_coe] at this
      rw [← hr]; exact WithTop.coe_le_coe.mpr this
  · intro X
    by_cases hgX : g X = ⊤
    · rw [hgX]; exact le_top
    obtain ⟨G, hG⟩ := WithTop.ne_top_iff_exists.mp hgX
    by_cases h1 : tail a ∈ X <;> by_cases h2 : head a ∈ X
    · have h := hy X
      rw [f0 X (by simp [h1, h2]), add_zero] at h
      simpa [dd, h1, h2] using h
    · have := htH _ ((hHs X).mpr ⟨h1, h2, hgX⟩)
      rw [hhis, ← hG, WithTop.untopD_coe] at this
      rw [← hG]
      simp only [dd, h1, h2, if_true, if_false]
      exact WithTop.coe_le_coe.mpr (by linarith)
    · have := htL _ ((hLs X).mpr ⟨h2, h1, hgX⟩)
      rw [hlos, ← hG, WithTop.untopD_coe] at this
      rw [← hG]
      simp only [dd, h1, h2, if_true, if_false]
      exact WithTop.coe_le_coe.mpr (by linarith)
    · have h := hy X
      rw [f0 X (by simp [h1, h2]), add_zero] at h
      simpa [dd, h1, h2] using h
  · intro hcI hcuI hgI hyI
    rcases htw with ⟨i, hi, hit⟩ | ⟨j, hj, hjt⟩ | h0
    · cases i with
      | none =>
        obtain ⟨r, hr⟩ := WithBot.ne_bot_iff_exists.mp (hLn.mp hi)
        rw [hlon, ← hr, WithBot.unbotD_coe] at hit
        rw [← hit]; exact hcI r hr.symm
      | some Y =>
        obtain ⟨G, hG⟩ := WithTop.ne_top_iff_exists.mp ((hLs Y).mp hi).2.2
        rw [hlos, ← hG, WithTop.untopD_coe] at hit
        rw [← hit]; exact intSub (intSum y hyI Y) (hgI Y G hG.symm)
    · cases j with
      | none =>
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (hHn.mp hj)
        rw [hhin, ← hr, WithTop.untopD_coe] at hjt
        rw [← hjt]; exact hcuI r hr.symm
      | some X =>
        obtain ⟨G, hG⟩ := WithTop.ne_top_iff_exists.mp ((hHs X).mp hj).2.2
        rw [hhis, ← hG, WithTop.untopD_coe] at hjt
        rw [← hjt]; exact intSub (hgI X G hG.symm) (intSum y hyI X)
    · exact ⟨0, by simp [h0]⟩

/-! ### Feasibility by induction over the arcs -/

lemma IntW_arcF {V A : Type*} [DecidableEq V] (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (hU : IsIntegerUpper cUpper) (hL : IsIntegerLower cLower)
    (a : A) (X : Finset V) : IntW (arcF tail head cUpper cLower a X) := by
  unfold arcF
  refine IntW_add ?_ ?_
  · split_ifs
    · exact IntW_N (hL a)
    · exact IntW_zero
  · split_ifs
    · exact fun r hr => hU a r hr
    · exact IntW_zero

theorem core {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (hbox : ∀ a, ∃ t : ℝ, cLower a ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cUpper a)
    (ρ : Finset V → WithTop ℝ) (hρ : Submodular ρ) (I : Prop)
    (hI : I → IsIntegerUpper cUpper ∧ IsIntegerLower cLower ∧ IsIntegerUpper ρ) (S : Finset A) :
    ∀ y : V → ℝ, (I → ∀ v, ∃ n : ℤ, (n : ℝ) = y v) →
    (∀ X : Finset V, ((∑ v ∈ X, y v : ℝ) : WithTop ℝ) ≤
      ρ X + ∑ a ∈ S, arcF tail head cUpper cLower a X) →
    ∃ ξ : A → ℝ, (∀ a ∈ S, cLower a ≤ (ξ a : WithBot ℝ) ∧ (ξ a : WithTop ℝ) ≤ cUpper a) ∧
      (I → ∀ a, ∃ n : ℤ, (n : ℝ) = ξ a) ∧
      ∀ X : Finset V,
        ((∑ v ∈ X, y v + ∑ a ∈ S, ξ a * dd tail head a X : ℝ) : WithTop ℝ) ≤ ρ X := by
  induction S using Finset.induction_on with
  | empty =>
    intro y _ hy
    refine ⟨fun _ => 0, by simp, fun _ _ => ⟨0, by simp⟩, ?_⟩
    intro X; simpa using hy X
  | insert a S ha ih =>
    intro y hyI hy
    have hg : Submodular (fun X => ρ X + ∑ b ∈ S, arcF tail head cUpper cLower b X) :=
      submod_add hρ (submod_sum S _ (fun b _ => arcF_submod tail head cUpper cLower b (hbox b)))
    have hy' : ∀ X : Finset V, ((∑ v ∈ X, y v : ℝ) : WithTop ℝ) ≤
        (ρ X + ∑ b ∈ S, arcF tail head cUpper cLower b X) + arcF tail head cUpper cLower a X := by
      intro X
      have := hy X
      rw [Finset.sum_insert ha] at this
      calc _ ≤ _ := this
        _ = _ := by rw [add_comm (arcF tail head cUpper cLower a X), add_assoc]
    obtain ⟨t, ht1, ht2, ht3, ht4⟩ := arc_elim tail head cUpper cLower a (hbox a) _ hg y hy'
    have htI : I → ∃ m : ℤ, (m : ℝ) = t := by
      intro hI'
      obtain ⟨hU, hL, hR⟩ := hI hI'
      exact ht4 (hL a) (fun r hr => hU a r hr)
        (fun X => IntW_add (fun r hr => hR X r hr)
          (IntW_sum _ _ (fun b _ => IntW_arcF tail head cUpper cLower hU hL b X))) (hyI hI')
    let y' : V → ℝ := fun v =>
      y v + t * ((if tail a = v then 1 else 0) - (if head a = v then 1 else 0))
    have hy'sum : ∀ X : Finset V, ∑ v ∈ X, y' v = ∑ v ∈ X, y v + t * dd tail head a X := by
      intro X
      simp only [y', dd, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
        Finset.sum_ite_eq]
    have hy'I : I → ∀ v, ∃ n : ℤ, (n : ℝ) = y' v := by
      intro hI' v
      obtain ⟨m, hm⟩ := htI hI'
      obtain ⟨n, hn⟩ := hyI hI' v
      refine ⟨n + m * ((if tail a = v then 1 else 0) - (if head a = v then 1 else 0)), ?_⟩
      simp only [y']
      rw [← hn, ← hm]
      split_ifs <;> push_cast <;> ring
    have hy'le : ∀ X : Finset V, ((∑ v ∈ X, y' v : ℝ) : WithTop ℝ) ≤
        ρ X + ∑ b ∈ S, arcF tail head cUpper cLower b X := by
      intro X; rw [hy'sum]; exact ht3 X
    obtain ⟨ξ, hξ1, hξ2, hξ3⟩ := ih y' hy'I hy'le
    refine ⟨Function.update ξ a t, ?_, ?_, ?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · simp only [Function.update_apply, if_true]; exact ⟨ht1, ht2⟩
      · have hne : b ≠ a := fun h => ha (h ▸ hb)
        simp only [Function.update_apply, hne, if_false]; exact hξ1 b hb
    · intro hI' b
      by_cases hb : b = a
      · simp only [Function.update_apply, hb, if_true]; exact htI hI'
      · simp only [Function.update_apply, hb, if_false]; exact hξ2 hI' b
    · intro X
      rw [Finset.sum_insert ha]
      have hS : ∑ b ∈ S, Function.update ξ a t b * dd tail head b X =
          ∑ b ∈ S, ξ b * dd tail head b X := by
        refine Finset.sum_congr rfl (fun b hb => ?_)
        have hne : b ≠ a := fun h => ha (h ▸ hb)
        simp only [Function.update_apply, hne, if_false]
      rw [hS]
      have h3 := hξ3 X
      rw [hy'sum] at h3
      simp only [Function.update_apply, if_true]
      calc ((∑ v ∈ X, y v + (t * dd tail head a X + ∑ b ∈ S, ξ b * dd tail head b X) : ℝ) :
            WithTop ℝ)
          = ((∑ v ∈ X, y v + t * dd tail head a X + ∑ b ∈ S, ξ b * dd tail head b X : ℝ) :
            WithTop ℝ) := by rw [add_assoc]
        _ ≤ ρ X := h3

lemma fiber_sum {V A : Type*} [Fintype A] [DecidableEq V] (f : A → V) (ξ : A → ℝ)
    (X : Finset V) :
    ∑ v ∈ X, ∑ a ∈ Finset.univ.filter (fun a => f a = v), ξ a =
      ∑ a, if f a ∈ X then ξ a else 0 := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  exact Finset.sum_ite_eq X (f a) (fun _ => ξ a)

lemma bsum {V A : Type*} [Fintype A] [DecidableEq V] (tail head : A → V) (ξ : A → ℝ)
    (X : Finset V) :
    ∑ v ∈ X, Boundary tail head ξ v = ∑ a, ξ a * dd tail head a X := by
  simp only [Boundary]
  rw [Finset.sum_sub_distrib, fiber_sum, fiber_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [dd]
  split_ifs <;> ring

lemma arc_nec {V A : Type*} [DecidableEq V] (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (a : A) (x : ℝ)
    (h1 : cLower a ≤ (x : WithBot ℝ)) (h2 : (x : WithTop ℝ) ≤ cUpper a) (X : Finset V) :
    ((-(x * dd tail head a X) : ℝ) : WithTop ℝ) ≤ arcF tail head cUpper cLower a X := by
  by_cases ht : tail a ∈ X <;> by_cases hh : head a ∈ X
  · simp [arcF, dd, ht, hh]
  · simpa [arcF, dd, ht, hh] using N_ge h1
  · simpa [arcF, dd, ht, hh] using h2
  · simp [arcF, dd, ht, hh]

lemma nec_sum {V A : Type*} [DecidableEq V] (tail head : A → V) (cUpper : A → WithTop ℝ)
    (cLower : A → WithBot ℝ) (T : Finset A) (ξ : A → ℝ)
    (hb : ∀ a ∈ T, cLower a ≤ (ξ a : WithBot ℝ) ∧ (ξ a : WithTop ℝ) ≤ cUpper a) (X : Finset V) :
    ((-(∑ a ∈ T, ξ a * dd tail head a X) : ℝ) : WithTop ℝ) ≤
      ∑ a ∈ T, arcF tail head cUpper cLower a X := by
  rw [← Finset.sum_neg_distrib, WithTop.coe_sum]
  exact Finset.sum_le_sum (fun a ha => arc_nec tail head cUpper cLower a (ξ a) (hb a ha).1
    (hb a ha).2 X)

lemma nec_cut {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] (tail head : A → V)
    (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (ρ : Finset V → WithTop ℝ) (ξ : A → ℝ)
    (hF : FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ) (X : Finset V) :
    (0 : WithTop ℝ) ≤ ρ X + ∑ a, arcF tail head cUpper cLower a X := by
  have hb := hF.2.1 X
  rw [bsum] at hb
  have hn := nec_sum tail head cUpper cLower Finset.univ ξ (fun a _ => hF.1 a) X
  calc (0 : WithTop ℝ) = ((∑ a, ξ a * dd tail head a X : ℝ) : WithTop ℝ) +
        ((-(∑ a, ξ a * dd tail head a X) : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]; simp
    _ ≤ ρ X + ∑ a, arcF tail head cUpper cLower a X := add_le_add hb hn

theorem feas {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
    (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (hbox : ∀ a, ∃ t : ℝ, cLower a ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cUpper a)
    (ρ : Finset V → WithTop ℝ) (hρ : Submodular ρ) (I : Prop)
    (hI : I → IsIntegerUpper cUpper ∧ IsIntegerLower cLower ∧ IsIntegerUpper ρ)
    (hcut : ∀ X : Finset V, (0 : WithTop ℝ) ≤ ρ X + ∑ a, arcF tail head cUpper cLower a X) :
    ∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ ∧
      (I → ∀ a, ∃ n : ℤ, (n : ℝ) = ξ a) := by
  obtain ⟨ξ, h1, h2, h3⟩ := core tail head cUpper cLower hbox ρ hρ I hI Finset.univ (fun _ => 0)
    (fun _ _ => ⟨0, by simp⟩) (fun X => by simpa using hcut X)
  refine ⟨ξ, ⟨fun a => h1 a (Finset.mem_univ a), fun X => ?_, ?_⟩, h2⟩
  · rw [bsum]; simpa using h3 X
  · rw [bsum]; simp [dd]

lemma erase_ident {V A : Type*} [Fintype A] [DecidableEq V] [DecidableEq A] (tail head : A → V)
    (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ) (a0 : A) (X : Finset V)
    (h : a0 ∈ DeltaPlus tail head X) :
    ∑ a ∈ Finset.univ.erase a0, arcF tail head cUpper cLower a X =
      UpperCapOf cUpper (DeltaMinus tail head X) +
        NegLowerCapOf cLower ((DeltaPlus tail head X).erase a0) := by
  have h' : tail a0 ∈ X ∧ head a0 ∉ X := by simpa [DeltaPlus] using h
  simp only [arcF, Finset.sum_add_distrib, UpperCapOf, NegLowerCapOf, DeltaPlus, DeltaMinus,
    ← Finset.sum_filter, Finset.filter_erase]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.erase_eq_self.mpr
  simp [h'.1]

lemma neg_add_nonneg_of_le {k : ℝ} {T : WithTop ℝ} (h : (k : WithTop ℝ) ≤ T) :
    (0 : WithTop ℝ) ≤ ((-k : ℝ) : WithTop ℝ) + T := by
  induction T using WithTop.recTopCoe with
  | top => simp
  | coe s =>
    have := WithTop.coe_le_coe.mp h
    rw [← WithTop.coe_add]
    exact_mod_cast (by linarith : (0 : ℝ) ≤ -k + s)

lemma sup_ge {s m : WithTop ℝ} (h : ∀ k : ℝ, (k : WithTop ℝ) ≤ m → (k : WithTop ℝ) ≤ s) :
    m ≤ s := by
  induction m using WithTop.recTopCoe with
  | top =>
    induction s using WithTop.recTopCoe with
    | top => exact le_rfl
    | coe r =>
      exfalso
      have := WithTop.coe_le_coe.mp (h (r + 1) le_top)
      linarith
  | coe r => exact h r le_rfl

end P8c535099

open DiscreteConvex.NetworkFlows in
theorem solution {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V]
    [DecidableEq A] (tail head : A → V) (cUpper : A → WithTop ℝ) (cLower : A → WithBot ℝ)
    (ρ : Finset V → WithTop ℝ) (hρ : Submodular ρ) (hρEmpty : ρ ∅ = 0)
    (hρV : ρ (Finset.univ : Finset V) = 0) (a0 : A)
    (hfeas : ∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ) :
    (sSup {v : WithTop ℝ | ∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ ∧
        v = (ξ a0 : WithTop ℝ)} =
      min (cUpper a0)
        ((Finset.univ.filter (fun X : Finset V => a0 ∈ DeltaPlus tail head X)).inf
          (fun X => UpperCapOf cUpper (DeltaMinus tail head X) +
            NegLowerCapOf cLower ((DeltaPlus tail head X).erase a0) + ρ X))) ∧
    (IsIntegerUpper cUpper → IsIntegerLower cLower → IsIntegerUpper ρ →
      (sSup {v : WithTop ℝ | ∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ ∧
          v = (ξ a0 : WithTop ℝ)} ≠ ⊤) →
      ∃ ξ : A → ℤ, FeasibleFlowMSFP1 tail head cUpper cLower ρ (fun a => (ξ a : ℝ)) ∧
        ∀ ξ' : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ' → ξ' a0 ≤ (ξ a0 : ℝ)) := by
  obtain ⟨ξ0, hξ0⟩ := hfeas
  set m : WithTop ℝ := min (cUpper a0)
    ((Finset.univ.filter (fun X : Finset V => a0 ∈ DeltaPlus tail head X)).inf
      (fun X => UpperCapOf cUpper (DeltaMinus tail head X) +
        NegLowerCapOf cLower ((DeltaPlus tail head X).erase a0) + ρ X)) with hm
  set Sset := {v : WithTop ℝ | ∃ ξ : A → ℝ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ ∧
        v = (ξ a0 : WithTop ℝ)} with hS
  -- weak duality
  have weak : ∀ ξ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ → (ξ a0 : WithTop ℝ) ≤ m := by
    intro ξ hF
    refine le_min (hF.1 a0).2 (Finset.le_inf (fun X hX => ?_))
    have hX' : a0 ∈ DeltaPlus tail head X := (Finset.mem_filter.mp hX).2
    have h' : tail a0 ∈ X ∧ head a0 ∉ X := by simpa [DeltaPlus] using hX'
    have hb := hF.2.1 X
    rw [P8c535099.bsum] at hb
    have hsplit : ∑ a, ξ a * P8c535099.dd tail head a X =
        ξ a0 + ∑ a ∈ Finset.univ.erase a0, ξ a * P8c535099.dd tail head a X := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
      simp [P8c535099.dd, h'.1, h'.2]
    have hn := P8c535099.nec_sum tail head cUpper cLower (Finset.univ.erase a0) ξ (fun a _ => hF.1 a) X
    rw [← P8c535099.erase_ident tail head cUpper cLower a0 X hX']
    calc (ξ a0 : WithTop ℝ) = ((∑ a, ξ a * P8c535099.dd tail head a X : ℝ) : WithTop ℝ) +
          ((-(∑ a ∈ Finset.univ.erase a0, ξ a * P8c535099.dd tail head a X) : ℝ) : WithTop ℝ) := by
            rw [← WithTop.coe_add, hsplit]; congr 1; ring
      _ ≤ ρ X + ∑ a ∈ Finset.univ.erase a0, P8c535099.arcF tail head cUpper cLower a X := add_le_add hb hn
      _ = _ := add_comm _ _
  -- strong duality
  have strong : ∀ k : ℝ, (k : WithTop ℝ) ≤ m → ∀ I : Prop,
      (I → IsIntegerUpper cUpper ∧ IsIntegerLower cLower ∧ IsIntegerUpper ρ ∧
        ∃ n : ℤ, (n : ℝ) = k) →
      ∃ ξ, FeasibleFlowMSFP1 tail head cUpper cLower ρ ξ ∧ k ≤ ξ a0 ∧
        (I → ∀ a, ∃ n : ℤ, (n : ℝ) = ξ a) := by
    intro k hk I hI
    set cL' : A → WithBot ℝ := Function.update cLower a0 (max (cLower a0) (k : WithBot ℝ))
      with hcL'
    have hkU : (k : WithTop ℝ) ≤ cUpper a0 := hk.trans (min_le_left _ _)
    have hbox' : ∀ a, ∃ t : ℝ, cL' a ≤ (t : WithBot ℝ) ∧ (t : WithTop ℝ) ≤ cUpper a := by
      intro a
      by_cases ha : a = a0
      · rw [ha]
        refine ⟨max (ξ0 a0) k, ?_, ?_⟩
        · simp only [cL', Function.update_apply, if_true]
          exact max_le ((hξ0.1 a0).1.trans (WithBot.coe_le_coe.mpr (le_max_left _ _)))
            (WithBot.coe_le_coe.mpr (le_max_right _ _))
        · rw [WithTop.coe_max]
          exact max_le (hξ0.1 a0).2 hkU
      · refine ⟨ξ0 a, ?_, (hξ0.1 a).2⟩
        simp only [cL', Function.update_apply, ha, if_false]; exact (hξ0.1 a).1
    have hcut' : ∀ X, (0 : WithTop ℝ) ≤ ρ X + ∑ a, P8c535099.arcF tail head cUpper cL' a X := by
      intro X
      have hsame : ∀ a ∈ Finset.univ.erase a0,
          P8c535099.arcF tail head cUpper cL' a X = P8c535099.arcF tail head cUpper cLower a X := by
        intro a ha
        have hne := Finset.ne_of_mem_erase ha
        simp only [P8c535099.arcF, cL', Function.update_apply, hne, if_false]
      have hnec := P8c535099.nec_cut tail head cUpper cLower ρ ξ0 hξ0 X
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0), Finset.sum_congr rfl hsame]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)] at hnec
      by_cases hX : tail a0 ∈ X ∧ head a0 ∉ X
      · rcases le_total (k : WithBot ℝ) (cLower a0) with hkc | hkc
        · have : P8c535099.arcF tail head cUpper cL' a0 X = P8c535099.arcF tail head cUpper cLower a0 X := by
            simp only [P8c535099.arcF, cL', Function.update_apply, if_true, max_eq_left hkc]
          rw [this]; exact hnec
        · have hval : P8c535099.arcF tail head cUpper cL' a0 X = ((-k : ℝ) : WithTop ℝ) := by
            simp only [P8c535099.arcF, cL', Function.update_apply, if_true, max_eq_right hkc, P8c535099.N_coe,
              if_pos hX]
            rw [if_neg (fun h => hX.2 h.1), add_zero]
          rw [hval]
          have hXm : a0 ∈ DeltaPlus tail head X := by simp [DeltaPlus, hX.1, hX.2]
          have hle : (k : WithTop ℝ) ≤
              ρ X + ∑ a ∈ Finset.univ.erase a0, P8c535099.arcF tail head cUpper cLower a X := by
            have h1 := hk.trans (min_le_right _ _)
            have h2 := h1.trans (Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ X, hXm⟩))
            rw [← P8c535099.erase_ident tail head cUpper cLower a0 X hXm] at h2
            rwa [add_comm] at h2
          rw [add_left_comm]
          exact P8c535099.neg_add_nonneg_of_le hle
      · have : P8c535099.arcF tail head cUpper cL' a0 X = P8c535099.arcF tail head cUpper cLower a0 X := by
          unfold P8c535099.arcF; rw [if_neg hX, if_neg hX]
        rw [this]; exact hnec
    have hI' : I → IsIntegerUpper cUpper ∧ IsIntegerLower cL' ∧ IsIntegerUpper ρ := by
      intro hi
      obtain ⟨hU, hL, hR, n, hn⟩ := hI hi
      refine ⟨hU, ?_, hR⟩
      intro a r hr
      by_cases ha : a = a0
      · rw [ha] at hr
        simp only [cL', Function.update_apply, if_true] at hr
        rcases max_choice (cLower a0) (k : WithBot ℝ) with h | h
        · rw [h] at hr; exact hL a0 r hr
        · rw [h] at hr
          exact ⟨n, by rw [hn]; exact WithBot.coe_injective hr⟩
      · simp only [cL', Function.update_apply, ha, if_false] at hr; exact hL a r hr
    obtain ⟨ξ, hF, hξI⟩ := P8c535099.feas tail head cUpper cL' hbox' ρ hρ I hI' hcut'
    refine ⟨ξ, ⟨fun a => ⟨?_, (hF.1 a).2⟩, hF.2.1, hF.2.2⟩, ?_, hξI⟩
    · by_cases ha : a = a0
      · rw [ha]
        have := (hF.1 a0).1
        simp only [cL', Function.update_apply, if_true] at this
        exact (le_max_left _ _).trans this
      · have := (hF.1 a).1
        simp only [cL', Function.update_apply, ha, if_false] at this
        exact this
    · have := (hF.1 a0).1
      simp only [cL', Function.update_apply, if_true] at this
      exact WithBot.coe_le_coe.mp ((le_max_right _ _).trans this)
  -- the supremum
  have hsup : sSup Sset = m := by
    have hne : Sset.Nonempty := ⟨_, ξ0, hξ0, rfl⟩
    have hbdd : BddAbove Sset := ⟨⊤, fun _ _ => le_top⟩
    apply le_antisymm
    · apply csSup_le hne
      rintro v ⟨ξ, hF, rfl⟩
      exact weak ξ hF
    · apply P8c535099.sup_ge
      intro k hk
      obtain ⟨ξ, hF, hkξ, _⟩ := strong k hk False (fun h => h.elim)
      exact (WithTop.coe_le_coe.mpr hkξ).trans (le_csSup hbdd ⟨ξ, hF, rfl⟩)
  refine ⟨hsup, ?_⟩
  intro hU hL hR hfin
  rw [hsup] at hfin
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfin
  have hmI : P8c535099.IntW m := by
    refine P8c535099.IntW_min (fun s hs => hU a0 s hs) ?_
    refine Finset.inf_induction P8c535099.IntW_top (fun a ha b hb => P8c535099.IntW_min ha hb) ?_
    intro X _
    exact P8c535099.IntW_add (P8c535099.IntW_add (P8c535099.IntW_sum _ _ (fun a _ => fun s hs => hU a s hs))
      (P8c535099.IntW_sum _ _ (fun a _ => P8c535099.IntW_N (hL a)))) (fun s hs => hR X s hs)
  obtain ⟨n, hn⟩ := hmI r hr.symm
  obtain ⟨ξ, hF, hkξ, hξI⟩ := strong r hr.le True (fun _ => ⟨hU, hL, hR, n, hn⟩)
  let ξZ : A → ℤ := fun a => (hξI trivial a).choose
  have hZ : (fun a => (ξZ a : ℝ)) = ξ := funext (fun a => (hξI trivial a).choose_spec)
  refine ⟨ξZ, by rw [hZ]; exact hF, fun ξ' hF' => ?_⟩
  have h1 := weak ξ' hF'
  rw [← hr] at h1
  have h2 : ξ' a0 ≤ r := WithTop.coe_le_coe.mp h1
  have h3 : (ξZ a0 : ℝ) = ξ a0 := (hξI trivial a0).choose_spec
  rw [h3]; linarith
