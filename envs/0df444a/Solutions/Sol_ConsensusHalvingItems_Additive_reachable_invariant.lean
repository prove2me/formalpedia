-- Prove2me | solution 1 for ConsensusHalvingItems.Additive.reachable_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T22:27:14.413543+00:00
-- url     : https://prove2.me/submissions/3b40ac93-9f97-4423-86d3-943370e18005

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_loopStep
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving
import Definitions.Def_ConsensusHalvingItems_Additive_Reachable

set_option autoImplicit false

namespace ConsensusHalvingItems.Additive
namespace LSP

/-! ## Value of a ticked program (independent of the start counter) -/

theorem run_bind' {α β : Type} (p : StateM ℕ α) (f : α → StateM ℕ β) (t : ℕ) :
    (p >>= f).run t = (f (p.run t).1).run (p.run t).2 := rfl

def Val {α : Type} (p : StateM ℕ α) (a : α) : Prop := ∀ t, (p.run t).1 = a

theorem val_pure {α : Type} (a : α) : Val (pure a : StateM ℕ α) a := fun _ => rfl

theorem val_bind {α β : Type} {p : StateM ℕ α} {f : α → StateM ℕ β} {a : α} {b : β}
    (hp : Val p a) (hf : Val (f a) b) : Val (p >>= f) b := by
  intro t; rw [run_bind', hp t]; exact hf _

theorem val_tick (c : ℕ) : Val (tick c) () := fun _ => rfl
theorem val_qadd (a b : ℚ) : Val (qadd a b) (a + b) := fun _ => rfl
theorem val_qsub (a b : ℚ) : Val (qsub a b) (a - b) := fun _ => rfl
theorem val_qmul (a b : ℚ) : Val (qmul a b) (a * b) := fun _ => rfl
theorem val_qdiv (a b : ℚ) : Val (qdiv a b) (a / b) := fun _ => rfl
theorem val_qeq (a b : ℚ) : Val (qeq a b) (decide (a = b)) := fun _ => rfl
theorem val_qlt (a b : ℚ) : Val (qlt a b) (decide (a < b)) := fun _ => rfl
theorem val_uAt {n m : ℕ} (u : Fin n → Fin m → ℚ) (i : Fin n) (j : Fin m) :
    Val (uAt u i j) (u i j) := fun _ => rfl

theorem val_mapM {α β : Type} (f : α → StateM ℕ β) (g : α → β) (hf : ∀ a, Val (f a) (g a)) :
    ∀ l : List α, Val (l.mapM f) (l.map g)
  | [] => by simpa using val_pure ([] : List β)
  | a :: l => by
    rw [List.mapM_cons, List.map_cons]
    exact val_bind (hf a) (val_bind (val_mapM f g hf l) (val_pure _))

theorem val_foldlM {α β : Type} (f : β → α → StateM ℕ β) (g : β → α → β)
    (hf : ∀ b a, Val (f b a) (g b a)) :
    ∀ (l : List α) (b : β), Val (l.foldlM f b) (l.foldl g b)
  | [], b => by simpa using val_pure b
  | a :: l, b => by
    rw [List.foldlM_cons, List.foldl_cons]
    exact val_bind (hf b a) (val_foldlM f g hf l _)

theorem val_filterMapM {α β : Type} (f : α → StateM ℕ (Option β)) (g : α → Option β)
    (hf : ∀ a, Val (f a) (g a)) : ∀ l : List α, Val (l.filterMapM f) (l.filterMap g)
  | [] => by simpa using val_pure ([] : List β)
  | a :: l => by
    rw [List.filterMapM_cons, List.filterMap_cons]
    refine val_bind (hf a) ?_
    cases g a with
    | none => exact val_filterMapM f g hf l
    | some b => exact val_bind (val_filterMapM f g hf l) (val_pure _)

/-! ## Pure versions of the programs -/

def fpV (c : ℕ) : List (List ℚ) → Option (List ℚ × List (List ℚ))
  | [] => none
  | r :: rs =>
    if decide (r.getD c 0 = 0) = true then
      (match fpV c rs with
        | none => none
        | some (p, rest) => some (p, r :: rest))
    else some (r, rs)

def elimV (c : ℕ) (p r : List ℚ) : List ℚ :=
  (List.zip r p).map fun ab => ab.1 - r.getD c 0 * ab.2

def stepV {m : ℕ} (st : List (Fin m × List ℚ) × List (List ℚ)) (c : Fin m) :
    List (Fin m × List ℚ) × List (List ℚ) :=
  match fpV c.val st.2 with
  | none => st
  | some (p, rest) =>
    (st.1.map (fun qr => (qr.1, elimV c.val (p.map fun a => a / p.getD c.val 0) qr.2)) ++
      [(c, p.map fun a => a / p.getD c.val 0)],
     rest.map (elimV c.val (p.map fun a => a / p.getD c.val 0)))

def dV {m : ℕ} (piv : List (Fin m × List ℚ)) (f : Fin m) (c : Fin m) : ℚ :=
  if c = f then 1 else
    match piv.find? (fun pr => pr.1 == c) with
    | some (_, r) => 0 - r.getD f.val 0
    | none => 0

def finalV {m : ℕ} (piv : List (Fin m × List ℚ)) : Option (Fin m → ℚ) :=
  match (List.finRange m).find? (fun c => !(piv.any fun pr => pr.1 == c)) with
  | none => none
  | some f => some fun c => ((List.finRange m).map (dV piv f)).getD c.val 0

def kernelDirV {m : ℕ} (rows : List (Fin m → ℚ)) : Option (Fin m → ℚ) :=
  finalV ((List.finRange m).foldl stepV
    ([], rows.map fun r => (List.finRange m).map r)).1

def urowV {n m : ℕ} (u : Fin n → Fin m → ℚ) (i : Fin n) : Fin m → ℚ :=
  fun j => ((List.finRange m).map fun j => u i j).getD j.val 0

def findSolutionV {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) :
    Option (Fin m → ℚ) :=
  match kernelDirV ((List.finRange n).map (urowV u) ++
      (List.finRange m).filterMap fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none) with
  | none => none
  | some d => some fun j => ((List.finRange m).map fun j => x j + d j).getD j.val 0

def gam {m : ℕ} (x y : Fin m → ℚ) (j : Fin m) : ℚ :=
  if decide (x j < y j) = true then (1 - x j) / (y j - x j) else x j / (x j - y j)

def Fv {m : ℕ} (x y : Fin m → ℚ) (acc : Option (Fin m × ℚ)) (j : Fin m) :
    Option (Fin m × ℚ) :=
  if decide (y j = x j) = true then acc else
    match acc with
    | none => some (j, gam x y j)
    | some (_, g0) => if decide (gam x y j < g0) = true then some (j, gam x y j) else acc

def loopStepV {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) :
    Option (Finset (Fin m) × (Fin m → ℚ)) :=
  match findSolutionV u T x with
  | none => none
  | some y =>
    match (List.finRange m).foldl (Fv x y) none with
    | none => none
    | some (js, g) =>
      some (insert js T, fun j => ((List.finRange m).map fun j => (1 - g) * x j + g * y j).getD j.val 0)

/-! ## The programs compute their pure versions -/

theorem val_findPivot (c : ℕ) : ∀ l : List (List ℚ), Val (kernelDir.findPivot c l) (fpV c l)
  | [] => by rw [kernelDir.findPivot]; exact val_pure _
  | r :: rs => by
    rw [kernelDir.findPivot, fpV]
    refine val_bind (val_tick _) (val_bind (val_qeq _ _) ?_)
    cases decide (r.getD c 0 = 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact val_pure _
    · simp only [↓reduceIte]
      refine val_bind (val_findPivot c rs) ?_
      cases fpV c rs with
      | none => exact val_pure _
      | some pr => exact val_pure _

theorem val_elim (c : ℕ) (p r : List ℚ) : Val (kernelDir.elim c p r) (elimV c p r) := by
  unfold kernelDir.elim elimV
  exact val_mapM _ _ (fun ab => by
    rcases ab with ⟨a, b⟩
    exact val_bind (val_tick _) (val_bind (val_qmul _ _) (val_qsub _ _))) _

theorem val_kernelDir {m : ℕ} (rows : List (Fin m → ℚ)) :
    Val (kernelDir rows) (kernelDirV rows) := by
  unfold kernelDir kernelDirV
  refine val_bind (val_mapM _ (fun (r : Fin m → ℚ) => (List.finRange m).map r)
    (fun (r : Fin m → ℚ) => val_mapM _ (fun c => r c)
      (fun c => val_bind (val_tick _) (val_pure (r c))) _) _) ?_
  refine val_bind (val_foldlM _ stepV (fun st c => ?_) _ _) ?_
  · refine val_bind (val_tick _) ?_
    refine val_bind (val_findPivot _ _) ?_
    unfold stepV
    cases fpV c.val st.2 with
    | none => exact val_pure _
    | some pr =>
      obtain ⟨p, rest⟩ := pr
      dsimp only
      refine val_bind (val_mapM _ (fun a => a / p.getD c.val 0)
        (fun a => val_bind (val_tick _) (val_qdiv _ _)) _) ?_
      refine val_bind (val_mapM _
        (fun qr => (qr.1, elimV c.val (p.map fun a => a / p.getD c.val 0) qr.2))
        (fun qr => ?_) _) ?_
      · rcases qr with ⟨q, r⟩
        exact val_bind (val_elim _ _ _) (val_pure _)
      · refine val_bind (val_mapM _ _ (fun r => val_elim _ _ _) _) ?_
        exact val_pure _
  · generalize (List.finRange m).foldl stepV
      ([], rows.map fun r => (List.finRange m).map r) = st
    dsimp only
    refine val_bind (val_tick _) ?_
    unfold finalV
    cases (List.finRange m).find? (fun c => !(st.1.any fun pr => pr.1 == c)) with
    | none => exact val_pure _
    | some f =>
      refine val_bind (val_mapM _ (dV st.1 f) (fun c => ?_) _) (val_pure _)
      refine val_bind (val_tick _) ?_
      unfold dV
      by_cases hc : c = f
      · rw [if_pos hc, if_pos hc]
        exact val_pure _
      · rw [if_neg hc, if_neg hc]
        cases st.1.find? (fun pr => pr.1 == c) with
        | none => exact val_pure _
        | some pr =>
          obtain ⟨q, r⟩ := pr
          exact val_qsub _ _

theorem val_findSolution {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) : Val (findSolution u T x) (findSolutionV u T x) := by
  unfold findSolution findSolutionV
  refine val_bind (val_mapM _ (urowV u) (fun i => val_bind
    (val_mapM _ (fun j => u i j) (fun j => val_uAt u i j) _) (val_pure _)) _) ?_
  refine val_bind (val_filterMapM _
    (fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none)
    (fun j => val_bind (val_tick _) (val_pure _)) _) ?_
  refine val_bind (val_kernelDir _) ?_
  cases kernelDirV ((List.finRange n).map (urowV u) ++
      (List.finRange m).filterMap fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none) with
  | none => exact val_pure _
  | some d =>
    exact val_bind (val_mapM _ (fun j => x j + d j) (fun j => val_qadd _ _) _) (val_pure _)

theorem val_loopStep {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) : Val (loopStep u T x) (loopStepV u T x) := by
  unfold loopStep loopStepV
  refine val_bind (val_findSolution u T x) ?_
  cases findSolutionV u T x with
  | none => exact val_pure _
  | some y =>
    dsimp only
    refine val_bind (val_foldlM _ (Fv x y) (fun acc j => ?_) _ _) ?_
    · refine val_bind (val_tick _) (val_bind (val_qeq _ _) ?_)
      unfold Fv
      cases decide (y j = x j)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine val_bind (val_qlt _ _) ?_
        have hm : ∀ g : ℚ, Val (match acc with
            | none => pure (some (j, g))
            | some (_, g0) => do
              let lt ← qlt g g0
              pure (if lt then some (j, g) else acc) : StateM ℕ (Option (Fin m × ℚ)))
            (match acc with
            | none => some (j, g)
            | some (_, g0) => if decide (g < g0) = true then some (j, g) else acc) := by
          intro g
          cases acc with
          | none => exact val_pure _
          | some pr =>
            obtain ⟨j0, g0⟩ := pr
            exact val_bind (val_qlt _ _) (val_pure _)
        unfold gam
        cases decide (x j < y j)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact val_bind (val_qsub _ _) (val_bind (val_qdiv _ _) (hm _))
        · simp only [↓reduceIte]
          exact val_bind (val_qsub _ _) (val_bind (val_qsub _ _) (val_bind (val_qdiv _ _) (hm _)))
      · simp only [↓reduceIte]
        exact val_pure _
    · cases (List.finRange m).foldl (Fv x y) none with
      | none => exact val_pure _
      | some pr =>
        obtain ⟨js, g⟩ := pr
        dsimp only
        exact val_bind (val_mapM _ (fun j => (1 - g) * x j + g * y j)
          (fun j => val_bind (val_tick _) (val_bind (val_qsub _ _) (val_bind (val_qmul _ _)
            (val_bind (val_qmul _ _) (val_qadd _ _))))) _) (val_pure _)

/-! ## Soundness of the elimination -/

def dotL {m : ℕ} (r : List ℚ) (d : Fin m → ℚ) : ℚ := ∑ c : Fin m, r.getD c.val 0 * d c

theorem getD_map_finRange {m : ℕ} (f : Fin m → ℚ) (j : Fin m) :
    ((List.finRange m).map f).getD j.val 0 = f j := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem getD_map0 (f : ℚ → ℚ) (hf : f 0 = 0) :
    ∀ (l : List ℚ) (n : ℕ), (l.map f).getD n 0 = f (l.getD n 0)
  | [], n => by simp [hf]
  | a :: l, 0 => by simp
  | a :: l, n + 1 => by
    simp only [List.map_cons, List.getD_cons_succ]
    exact getD_map0 f hf l n

theorem getD_zipmap (s : ℚ) : ∀ (r p : List ℚ), r.length = p.length → ∀ n : ℕ,
    ((List.zip r p).map fun ab => ab.1 - s * ab.2).getD n 0 = r.getD n 0 - s * p.getD n 0
  | [], [], _, n => by simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: r, b :: p, _, 0 => by simp
  | a :: r, b :: p, h, n + 1 => by
    simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
    exact getD_zipmap s r p (by simpa using h) n

theorem getD_elim (c : ℕ) (p r : List ℚ) (h : r.length = p.length) (n : ℕ) :
    (elimV c p r).getD n 0 = r.getD n 0 - r.getD c 0 * p.getD n 0 :=
  getD_zipmap _ r p h n

theorem length_elim (c : ℕ) (p r : List ℚ) :
    (elimV c p r).length = min r.length p.length := by
  simp [elimV]

theorem dot_elim {m : ℕ} (c : ℕ) (p r : List ℚ) (h : r.length = p.length) (d : Fin m → ℚ) :
    dotL (elimV c p r) d = dotL r d - r.getD c 0 * dotL p d := by
  unfold dotL
  simp only [getD_elim c p r h]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem dot_scale {m : ℕ} (p : List ℚ) (pc : ℚ) (d : Fin m → ℚ) :
    dotL (p.map fun a => a / pc) d = dotL p d / pc := by
  unfold dotL
  simp only [getD_map0 (fun a => a / pc) (zero_div pc)]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem fpV_some (c : ℕ) : ∀ (l : List (List ℚ)) (p : List ℚ) (rest : List (List ℚ)),
    fpV c l = some (p, rest) →
      p ∈ l ∧ p.getD c 0 ≠ 0 ∧ (∀ r ∈ rest, r ∈ l) ∧ (∀ r ∈ l, r = p ∨ r ∈ rest)
  | [], p, rest, h => by simp [fpV] at h
  | r :: rs, p, rest, h => by
    rw [fpV] at h
    by_cases hz : r.getD c 0 = 0
    · rw [if_pos (by simpa using hz)] at h
      rcases hr : fpV c rs with _ | ⟨p1, rest1⟩
      · simp [hr] at h
      · simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3, h4⟩ := fpV_some c rs p1 rest1 hr
        refine ⟨List.mem_cons_of_mem _ h1, h2, ?_, ?_⟩
        · intro r' hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · simp
          · exact List.mem_cons_of_mem _ (h3 r' hr')
        · intro r' hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · right; simp
          · rcases h4 r' hr' with h | h
            · left; exact h
            · right; exact List.mem_cons_of_mem _ h
    · rw [if_neg (by simpa using hz)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, hz, fun r' hr' => List.mem_cons_of_mem _ hr', fun r' hr' => List.mem_cons.mp hr'⟩

theorem fpV_none (c : ℕ) : ∀ l : List (List ℚ), fpV c l = none → ∀ r ∈ l, r.getD c 0 = 0
  | [], _, r, hr => by simp at hr
  | r :: rs, h, r', hr' => by
    rw [fpV] at h
    by_cases hz : r.getD c 0 = 0
    · rw [if_pos (by simpa using hz)] at h
      rcases hr : fpV c rs with _ | ⟨p1, rest1⟩
      · rcases List.mem_cons.mp hr' with rfl | hr'
        · exact hz
        · exact fpV_none c rs hr r' hr'
      · simp [hr] at h
    · rw [if_neg (by simpa using hz)] at h
      simp at h

def KInv {m : ℕ} (rows : List (Fin m → ℚ)) (S : Fin m → Prop)
    (st : List (Fin m × List ℚ) × List (List ℚ)) : Prop :=
  (∀ qr ∈ st.1, qr.2.length = m) ∧ (∀ r ∈ st.2, r.length = m) ∧
  (∀ qr ∈ st.1, qr.2.getD qr.1.val 0 = 1 ∧ S qr.1) ∧
  (∀ qr ∈ st.1, ∀ qr' ∈ st.1, qr'.1 ≠ qr.1 → qr.2.getD qr'.1.val 0 = 0) ∧
  (st.1.map Prod.fst).Nodup ∧
  (∀ r ∈ st.2, ∀ c : Fin m, S c → r.getD c.val 0 = 0) ∧
  (∀ d : Fin m → ℚ, (∀ qr ∈ st.1, dotL qr.2 d = 0) → (∀ r ∈ st.2, dotL r d = 0) →
    ∀ r ∈ rows, ∑ c, r c * d c = 0)

theorem kinv_step {m : ℕ} (rows : List (Fin m → ℚ)) (S : Fin m → Prop)
    (st : List (Fin m × List ℚ) × List (List ℚ)) (c : Fin m) (hc : ¬ S c)
    (h : KInv rows S st) : KInv rows (fun k => S k ∨ k = c) (stepV st c) := by
  obtain ⟨hL1, hL2, hP1, hP2, hN, hR, hS⟩ := h
  unfold stepV
  rcases hf : fpV c.val st.2 with _ | ⟨p, rest⟩
  · have h0 := fpV_none c.val st.2 hf
    refine ⟨hL1, hL2, fun qr hq => ⟨(hP1 qr hq).1, Or.inl (hP1 qr hq).2⟩, hP2, hN, ?_, hS⟩
    intro r hr k hk
    rcases hk with hk | rfl
    · exact hR r hr k hk
    · exact h0 r hr
  · obtain ⟨hp, hpc, hrest, hcov⟩ := fpV_some c.val st.2 p rest hf
    dsimp only
    have hpl : p.length = m := hL2 p hp
    have hp'l : (p.map fun a => a / p.getD c.val 0).length = m := by simp [hpl]
    have hp'g : ∀ j : ℕ, (p.map fun a => a / p.getD c.val 0).getD j 0 =
        p.getD j 0 / p.getD c.val 0 :=
      fun j => getD_map0 (fun a => a / p.getD c.val 0) (zero_div _) p j
    have hp'c : (p.map fun a => a / p.getD c.val 0).getD c.val 0 = 1 := by
      rw [hp'g]; exact div_self hpc
    have hp'S : ∀ k : Fin m, S k → (p.map fun a => a / p.getD c.val 0).getD k.val 0 = 0 :=
      fun k hk => by rw [hp'g, hR p hp k hk, zero_div]
    have hEl : ∀ r : List ℚ, r.length = m → ∀ j : ℕ,
        (elimV c.val (p.map fun a => a / p.getD c.val 0) r).getD j 0 =
          r.getD j 0 - r.getD c.val 0 * (p.map fun a => a / p.getD c.val 0).getD j 0 :=
      fun r hr j => getD_elim _ _ r (by rw [hr, hp'l]) j
    have hElL : ∀ r : List ℚ, r.length = m →
        (elimV c.val (p.map fun a => a / p.getD c.val 0) r).length = m :=
      fun r hr => by rw [length_elim, hr, hp'l, min_self]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro qr hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨qr0, hq0, rfl⟩ := List.mem_map.mp hq
        exact hElL _ (hL1 qr0 hq0)
      · rw [List.mem_singleton] at hq; subst hq; exact hp'l
    · intro r hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      exact hElL _ (hL2 r0 (hrest r0 hr0))
    · intro qr hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨qr0, hq0, rfl⟩ := List.mem_map.mp hq
        refine ⟨?_, Or.inl (hP1 qr0 hq0).2⟩
        dsimp only
        rw [hEl _ (hL1 qr0 hq0), hp'S _ (hP1 qr0 hq0).2, (hP1 qr0 hq0).1, mul_zero, sub_zero]
      · rw [List.mem_singleton] at hq; subst hq
        exact ⟨hp'c, Or.inr rfl⟩
    · intro qr hq qr' hq' hne
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨qr0, hq0, rfl⟩ := List.mem_map.mp hq
        dsimp only at hne ⊢
        rw [hEl _ (hL1 qr0 hq0)]
        rcases List.mem_append.mp hq' with hq' | hq'
        · obtain ⟨qr1, hq1, rfl⟩ := List.mem_map.mp hq'
          dsimp only at hne ⊢
          rw [hP2 qr0 hq0 qr1 hq1 hne, hp'S _ (hP1 qr1 hq1).2, mul_zero, sub_zero]
        · rw [List.mem_singleton] at hq'; subst hq'
          dsimp only
          rw [hp'c, mul_one, sub_self]
      · rw [List.mem_singleton] at hq; subst hq
        rcases List.mem_append.mp hq' with hq' | hq'
        · obtain ⟨qr1, hq1, rfl⟩ := List.mem_map.mp hq'
          exact hp'S _ (hP1 qr1 hq1).2
        · rw [List.mem_singleton] at hq'; subst hq'
          exact absurd rfl hne
    · rw [List.map_append, List.map_map, List.nodup_append_comm]
      have e : (Prod.fst ∘ fun qr : Fin m × List ℚ =>
          (qr.1, elimV c.val (p.map fun a => a / p.getD c.val 0) qr.2)) = Prod.fst := rfl
      rw [e]
      simp only [List.map_cons, List.map_nil, List.singleton_append, List.nodup_cons]
      refine ⟨fun hm => ?_, hN⟩
      obtain ⟨qr, hq, hqc⟩ := List.mem_map.mp hm
      exact hc (hqc ▸ (hP1 qr hq).2)
    · intro r hr k hk
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      have hr0' := hrest r0 hr0
      rw [hEl _ (hL2 r0 hr0')]
      rcases hk with hk | rfl
      · rw [hR r0 hr0' k hk, hp'S k hk, mul_zero, sub_zero]
      · rw [hp'c, mul_one, sub_self]
    · intro d hpiv hrst
      have hdp' : dotL (p.map fun a => a / p.getD c.val 0) d = 0 :=
        hpiv (c, p.map fun a => a / p.getD c.val 0) (by simp)
      have hdp : dotL p d = 0 := by
        rw [dot_scale] at hdp'
        rcases div_eq_zero_iff.mp hdp' with h | h
        · exact h
        · exact absurd h hpc
      have hE : ∀ r : List ℚ, r.length = m →
          dotL (elimV c.val (p.map fun a => a / p.getD c.val 0) r) d = 0 → dotL r d = 0 := by
        intro r hr h0
        rw [dot_elim _ _ _ (by rw [hr, hp'l]), hdp', mul_zero, sub_zero] at h0
        exact h0
      refine hS d (fun qr hq => ?_) (fun r hr => ?_)
      · exact hE _ (hL1 qr hq) (hpiv _ (List.mem_append_left _ (List.mem_map_of_mem hq)))
      · rcases hcov r hr with rfl | hr'
        · exact hdp
        · exact hE _ (hL2 r hr) (hrst _ (List.mem_map_of_mem hr'))

theorem kinv_foldl {m : ℕ} (rows : List (Fin m → ℚ)) :
    ∀ (l : List (Fin m)) (S : Fin m → Prop) (st : List (Fin m × List ℚ) × List (List ℚ)),
      l.Nodup → (∀ c ∈ l, ¬ S c) → KInv rows S st →
      KInv rows (fun k => S k ∨ k ∈ l) (l.foldl stepV st)
  | [], S, st, _, _, h => by
    have e : (fun k => S k ∨ k ∈ ([] : List (Fin m))) = S := by funext k; simp
    rw [List.foldl_nil, e]; exact h
  | c :: l, S, st, hnd, hdis, h => by
    rw [List.foldl_cons]
    have hnd' := List.nodup_cons.mp hnd
    have h1 := kinv_step rows S st c (hdis c (by simp)) h
    have h2 := kinv_foldl rows l (fun k => S k ∨ k = c) (stepV st c) hnd'.2
      (fun k hk hSk => hSk.elim (fun hs => hdis k (List.mem_cons_of_mem c hk) hs)
        (fun he => hnd'.1 (he ▸ hk))) h1
    have e : (fun k => (S k ∨ k = c) ∨ k ∈ l) = (fun k => S k ∨ k ∈ c :: l) := by
      funext k; apply propext; simp only [List.mem_cons]; tauto
    rw [← e]; exact h2

theorem kernel_sound {m : ℕ} (rows : List (Fin m → ℚ)) (d : Fin m → ℚ)
    (h : kernelDirV rows = some d) : ∀ r ∈ rows, ∑ c, r c * d c = 0 := by
  unfold kernelDirV at h
  have h0 : KInv rows (fun _ => False) ([], rows.map fun r => (List.finRange m).map r) := by
    refine ⟨by simp, ?_, by simp, by simp, by simp, fun _ _ _ hc => hc.elim, ?_⟩
    · intro r hr
      obtain ⟨r0, _, rfl⟩ := List.mem_map.mp hr
      simp
    · intro d _ hd r hr
      have := hd _ (List.mem_map.2 ⟨r, hr, rfl⟩)
      unfold dotL at this
      simpa only [getD_map_finRange] using this
  have hF := kinv_foldl rows (List.finRange m) _ _ (List.nodup_finRange m) (fun c _ h => h) h0
  generalize (List.finRange m).foldl stepV ([], rows.map fun r => (List.finRange m).map r) = st
    at h hF
  obtain ⟨_, _, hP1, hP2, hN, hR, hS⟩ := hF
  unfold finalV at h
  rcases hf : (List.finRange m).find? (fun c => !(st.1.any fun pr => pr.1 == c)) with _ | f
  · simp [hf] at h
  simp only [hf, Option.some.injEq] at h
  subst h
  have hfree : ∀ qr ∈ st.1, qr.1 ≠ f := by
    intro qr hq hqf
    have h1 := List.find?_some hf
    have h2 : (st.1.any fun pr => pr.1 == f) = true := List.any_eq_true.2 ⟨qr, hq, by simp [hqf]⟩
    simp [h2] at h1
  apply hS
  · intro qr hq
    unfold dotL
    simp only [getD_map_finRange]
    have hterm : ∀ c : Fin m, qr.2.getD c.val 0 * dV st.1 f c =
        (if c = qr.1 then -(qr.2.getD f.val 0) else 0) +
          (if c = f then qr.2.getD f.val 0 else 0) := by
      intro c
      unfold dV
      by_cases hcf : c = f
      · subst hcf
        have hne : c ≠ qr.1 := fun e => hfree qr hq e.symm
        rw [if_pos rfl, if_pos rfl, if_neg hne]
        ring
      · rw [if_neg hcf, if_neg hcf, add_zero]
        rcases hq2 : st.1.find? (fun pr => pr.1 == c) with _ | ⟨c', r'⟩
        · have hnone := List.find?_eq_none.mp hq2
          have hcq : c ≠ qr.1 := by
            intro e
            exact hnone qr hq (by simp [e])
          simp only [hq2, if_neg hcq]
          ring
        · have hm := List.mem_of_find?_eq_some hq2
          have hp := List.find?_some hq2
          have hc' : c' = c := by simpa using hp
          simp only [hq2]
          by_cases hcq : c = qr.1
          · rw [if_pos hcq]
            have e : (c', r') = qr :=
              List.inj_on_of_nodup_map hN hm hq (by simp [hc', hcq])
            subst e
            have h1 := (hP1 _ hq).1
            dsimp only at h1
            rw [← hc', h1]
            ring
          · rw [if_neg hcq]
            have := hP2 qr hq (c', r') hm (by simpa [hc'] using hcq)
            simp only [hc'] at this
            rw [this]
            ring
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp
  · intro r hr
    unfold dotL
    simp only [getD_map_finRange]
    apply Finset.sum_eq_zero
    intro c _
    rw [hR r hr c (Or.inr (List.mem_finRange c)), zero_mul]

theorem findSolution_sound {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x y : Fin m → ℚ) (h : findSolutionV u T x = some y) :
    ∃ d : Fin m → ℚ, (∀ i, ∑ j, u i j * d j = 0) ∧ ∀ j, y j = x j + d j := by
  unfold findSolutionV at h
  rcases hk : kernelDirV ((List.finRange n).map (urowV u) ++
      (List.finRange m).filterMap fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none)
    with _ | d
  · simp [hk] at h
  simp only [hk, Option.some.injEq] at h
  subst h
  refine ⟨d, fun i => ?_, fun j => getD_map_finRange _ j⟩
  have := kernel_sound _ d hk (urowV u i)
    (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
  simpa only [urowV, getD_map_finRange] using this

/-! ## The ratio scan -/

def Inv2 {m : ℕ} (x y : Fin m → ℚ) (S : Fin m → Prop) (acc : Option (Fin m × ℚ)) : Prop :=
  (∀ js g, acc = some (js, g) →
    y js ≠ x js ∧ g = gam x y js ∧ ∀ j, S j → y j ≠ x j → g ≤ gam x y j) ∧
  (acc = none → ∀ j, S j → y j = x j)

theorem inv2_step {m : ℕ} (x y : Fin m → ℚ) (S : Fin m → Prop) (acc : Option (Fin m × ℚ))
    (j : Fin m) (h : Inv2 x y S acc) : Inv2 x y (fun k => S k ∨ k = j) (Fv x y acc j) := by
  obtain ⟨h1, h2⟩ := h
  unfold Fv
  by_cases hj : y j = x j
  · rw [if_pos (by simpa using hj)]
    refine ⟨fun js g hacc => ?_, fun hacc k hk => ?_⟩
    · obtain ⟨a, b, c⟩ := h1 js g hacc
      refine ⟨a, b, fun k hk hne => ?_⟩
      rcases hk with hk | rfl
      · exact c k hk hne
      · exact absurd hj hne
    · rcases hk with hk | rfl
      · exact h2 hacc k hk
      · exact hj
  · rw [if_neg (by simpa using hj)]
    cases acc with
    | none =>
      dsimp only
      refine ⟨fun js g hacc => ?_, fun hacc => by cases hacc⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hacc
      obtain ⟨rfl, rfl⟩ := hacc
      refine ⟨hj, rfl, fun k hk hne => ?_⟩
      rcases hk with hk | rfl
      · exact absurd (h2 rfl k hk) hne
      · exact le_refl _
    | some pr =>
      obtain ⟨j0, g0⟩ := pr
      obtain ⟨a0, b0, c0⟩ := h1 j0 g0 rfl
      dsimp only
      by_cases hlt : gam x y j < g0
      · rw [if_pos (by simpa using hlt)]
        refine ⟨fun js g hacc => ?_, fun hacc => by cases hacc⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hacc
        obtain ⟨rfl, rfl⟩ := hacc
        refine ⟨hj, rfl, fun k hk hne => ?_⟩
        rcases hk with hk | rfl
        · exact le_of_lt (lt_of_lt_of_le hlt (c0 k hk hne))
        · exact le_refl _
      · rw [if_neg (by simpa using hlt)]
        refine ⟨fun js g hacc => ?_, fun hacc => by cases hacc⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hacc
        obtain ⟨rfl, rfl⟩ := hacc
        refine ⟨a0, b0, fun k hk hne => ?_⟩
        rcases hk with hk | rfl
        · exact c0 k hk hne
        · exact not_lt.1 hlt

theorem inv2_foldl {m : ℕ} (x y : Fin m → ℚ) :
    ∀ (l : List (Fin m)) (S : Fin m → Prop) (acc : Option (Fin m × ℚ)), Inv2 x y S acc →
      Inv2 x y (fun k => S k ∨ k ∈ l) (l.foldl (Fv x y) acc)
  | [], S, acc, h => by
    have e : (fun k => S k ∨ k ∈ ([] : List (Fin m))) = S := by funext k; simp
    rw [List.foldl_nil, e]; exact h
  | j :: l, S, acc, h => by
    rw [List.foldl_cons]
    have h2 := inv2_foldl x y l _ _ (inv2_step x y S acc j h)
    have e : (fun k => (S k ∨ k = j) ∨ k ∈ l) = (fun k => S k ∨ k ∈ j :: l) := by
      funext k; apply propext; simp only [List.mem_cons]; tauto
    rw [← e]; exact h2

theorem fold_spec {m : ℕ} (x y : Fin m → ℚ) (js : Fin m) (g : ℚ)
    (h : (List.finRange m).foldl (Fv x y) none = some (js, g)) :
    y js ≠ x js ∧ g = gam x y js ∧ ∀ j, y j ≠ x j → g ≤ gam x y j := by
  have h0 : Inv2 x y (fun _ => False) none := ⟨fun js g h => (by cases h), fun _ j hj => hj.elim⟩
  have := (inv2_foldl x y (List.finRange m) _ none h0).1 js g h
  exact ⟨this.1, this.2.1, fun j hj => this.2.2 j (Or.inr (List.mem_finRange j)) hj⟩

theorem gam_up {m : ℕ} (x y : Fin m → ℚ) (j : Fin m) (h : x j < y j) :
    gam x y j * (y j - x j) = 1 - x j := by
  unfold gam
  rw [if_pos (by simpa using h)]
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 h))

theorem gam_down {m : ℕ} (x y : Fin m → ℚ) (j : Fin m) (h : y j < x j) :
    gam x y j * (x j - y j) = x j := by
  unfold gam
  rw [if_neg (by simpa using not_lt.2 h.le)]
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 h))

theorem gam_nonneg {m : ℕ} (x y : Fin m → ℚ) (j : Fin m) (hf : 0 ≤ x j ∧ x j ≤ 1)
    (hne : y j ≠ x j) : 0 ≤ gam x y j := by
  unfold gam
  by_cases h : x j < y j
  · rw [if_pos (by simpa using h)]
    exact div_nonneg (sub_nonneg.2 hf.2) (sub_pos.2 h).le
  · rw [if_neg (by simpa using h)]
    have h' : y j < x j := lt_of_le_of_ne (not_lt.1 h) hne
    exact div_nonneg hf.1 (sub_pos.2 h').le


theorem findSolution_fix {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x y : Fin m → ℚ) (h : findSolutionV u T x = some y) : ∀ j ∈ T, y j = x j := by
  unfold findSolutionV at h
  rcases hk : kernelDirV ((List.finRange n).map (urowV u) ++
      (List.finRange m).filterMap fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none)
    with _ | d
  · simp [hk] at h
  simp only [hk, Option.some.injEq] at h
  subst h
  intro j hj
  have := kernel_sound _ d hk (Pi.single j (1 : ℚ))
    (List.mem_append_right _ (List.mem_filterMap.2 ⟨j, List.mem_finRange j, by simp [hj]⟩))
  simp [Pi.single_apply] at this
  show ((List.finRange m).map fun j => x j + d j).getD j.val 0 = x j
  rw [getD_map_finRange, this, add_zero]

theorem preserves {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (t : ℕ) (T' : Finset (Fin m)) (x' : Fin m → ℚ)
    (hx : IsConsensusHalving u x) (hstep : ((loopStep u T x).run t).1 = some (T', x')) :
    IsConsensusHalving u x' := by
  rw [LSP.val_loopStep u T x t] at hstep
  unfold LSP.loopStepV at hstep
  rcases hfs : LSP.findSolutionV u T x with _ | y
  · simp [hfs] at hstep
  simp only [hfs] at hstep
  rcases hb : (List.finRange m).foldl (LSP.Fv x y) none with _ | ⟨js, g⟩
  · simp [hb] at hstep
  simp only [hb, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨-, hx'⟩ := hstep
  have hx'j : ∀ j, x' j = x j + g * (y j - x j) := by
    intro j; rw [← hx']; simp only [LSP.getD_map_finRange]; ring
  obtain ⟨d, hd, hyd⟩ := LSP.findSolution_sound u T x y hfs
  obtain ⟨hjs, hg, hmin⟩ := LSP.fold_spec x y js g hb
  obtain ⟨hfrac, hhalf⟩ := hx
  have hg0 : 0 ≤ g := hg ▸ LSP.gam_nonneg x y js (hfrac js) hjs
  refine ⟨fun j => ?_, fun i => ?_⟩
  · rw [hx'j j]
    obtain ⟨h0, h1⟩ := hfrac j
    by_cases hj : y j = x j
    · rw [hj, sub_self, mul_zero, add_zero]; exact ⟨h0, h1⟩
    · have hgj := hmin j hj
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have hγ := LSP.gam_down x y j hlt
        have he : 0 ≤ x j - y j := (sub_pos.2 hlt).le
        have hA := mul_le_mul_of_nonneg_right hgj he
        have hC := mul_nonneg hg0 he
        constructor <;> linarith
      · have hγ := LSP.gam_up x y j hgt
        have he : 0 ≤ y j - x j := (sub_pos.2 hgt).le
        have hA := mul_le_mul_of_nonneg_right hgj he
        have hC := mul_nonneg hg0 he
        constructor <;> linarith
  · have e1 : additiveUtil u i x' = additiveUtil u i x + g * ∑ j, u i j * d j := by
      unfold additiveUtil
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hx'j j, hyd j]; ring
    have e2 : additiveUtil u i (fun j => 1 - x' j) =
        additiveUtil u i (fun j => 1 - x j) - g * ∑ j, u i j * d j := by
      unfold additiveUtil
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by dsimp only; rw [hx'j j, hyd j]; ring
    rw [e1, e2, hd i, mul_zero, add_zero, sub_zero]
    exact hhalf i

theorem freezes {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (t : ℕ) (T' : Finset (Fin m)) (x' : Fin m → ℚ)
    (hx : IsConsensusHalving u x) (hstep : ((loopStep u T x).run t).1 = some (T', x')) :
    ∃ js, js ∉ T ∧ T' = insert js T ∧ (x' js = 0 ∨ x' js = 1) ∧ ∀ j ∈ T, x' j = x j := by
  rw [LSP.val_loopStep u T x t] at hstep
  unfold LSP.loopStepV at hstep
  rcases hfs : LSP.findSolutionV u T x with _ | y
  · simp [hfs] at hstep
  simp only [hfs] at hstep
  rcases hb : (List.finRange m).foldl (LSP.Fv x y) none with _ | ⟨js, g⟩
  · simp [hb] at hstep
  simp only [hb, Option.some.injEq, Prod.mk.injEq] at hstep
  obtain ⟨hT, hx'⟩ := hstep
  have hx'j : ∀ j, x' j = x j + g * (y j - x j) := by
    intro j; rw [← hx']; simp only [LSP.getD_map_finRange]; ring
  have hfix := LSP.findSolution_fix u T x y hfs
  obtain ⟨hjs, hg, -⟩ := LSP.fold_spec x y js g hb
  refine ⟨js, fun hm => hjs (hfix js hm), hT.symm, ?_, fun j hj => ?_⟩
  · rcases lt_or_gt_of_ne hjs with hlt | hgt
    · left
      have h1 := LSP.gam_down x y js hlt
      rw [hx'j js, hg]
      linear_combination -h1
    · right
      have h1 := LSP.gam_up x y js hgt
      rw [hx'j js, hg]
      linear_combination h1
  · rw [hx'j j, hfix j hj, sub_self, mul_zero, add_zero]

theorem reach_inv {n m : ℕ} (u : Fin n → Fin m → ℚ) (p : Finset (Fin m) × (Fin m → ℚ))
    (h : Reachable u p) : IsConsensusHalving u p.2 ∧ ∀ j ∈ p.1, p.2 j = 0 ∨ p.2 j = 1 := by
  induction h with
  | init =>
    refine ⟨⟨fun j => ⟨by norm_num, by norm_num⟩, fun i => ?_⟩, fun j hj => by simp at hj⟩
    unfold additiveUtil
    exact Finset.sum_congr rfl fun j _ => by norm_num
  | @step T T' x x' _ hs ih =>
    obtain ⟨hcx, hT⟩ := ih
    have hp := preserves u T x 0 T' x' hcx hs
    obtain ⟨js, -, hT', hjs, hfix⟩ := freezes u T x 0 T' x' hcx hs
    refine ⟨hp, fun j hj => ?_⟩
    dsimp only at hj ⊢
    rw [hT', Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · exact hjs
    · rw [hfix j hj]; exact hT j hj

end LSP
end ConsensusHalvingItems.Additive

open ConsensusHalvingItems.Additive in
theorem solution {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (h : Reachable u (T, x)) :
    IsConsensusHalving u x ∧ ∀ j ∈ T, x j = 0 ∨ x j = 1 := by
  exact LSP.reach_inv u (T, x) h
